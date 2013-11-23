Require Import AutoSep.

Require Import VariableLemmas Syntax Semantics CompileStatement.
Require Import Malloc MyMalloc MyFree.
Require Import GeneralTactics.
Require Import GoodOptimizer.

Record func := {
  Name : string;
  Vars : list string;
  Body : Statement
}.

Definition funcSpec f : assert := st ~> Ex fs, funcsOk (fst st) fs
  /\ ExX, Ex vs, Ex a, Ex res,
    ![^[locals ("rp" :: "__reserved" :: "__arg" :: nil) vs res st#Sp * heap a * mallocHeap 0] * #0] st
    /\ [| res = wordToNat (sel vs "__reserved")
          /\ Safety.Safe fs (Body f) (vs, a) |]
    /\ (st#Rp, fst st) @@@ (st' ~> Ex vs', Ex a',
      [| st'#Sp = st#Sp |]
      /\ ![^[locals ("rp" :: "__reserved" :: "__arg" :: nil) vs' res st'#Sp * heap a' * mallocHeap 0] * #1] st'
      /\ [| exists vs'', RunsTo fs (Body f) (vs, a) (vs'', a') |] ).

Definition funcVars f := Vars f ++ tempChunk 0 (depth (Body f)).

Section Compiler.
  Variable optimizer : Statement -> Statement.

  Hypothesis optimizer_is_good_optimizer : is_good_optimizer optimizer.

  Variable moduleName : string.
  Definition modName := ("Cito_" ++ moduleName)%string.

  Definition funcBody f : forall imports, importsGlobal imports -> cmd imports modName := fun imports H =>
    Seq_ H
    (Straightline_ _ _
      (Assign (LvMem (Indir Sp 0)) Rp
        :: Assign Rv (LvMem (Indir Sp 4))
        :: nil))
    (Structured.If_ H Rv IL.Lt (length (funcVars f) + MIN_RESERVED)
      (* Not enough stack space remaining!  Time to freak out. *)
      (Diverge_ _ _)
      (* We have enough stack space, so start running the body. *)
      (Seq_ H
        (Seq_ H
          (Straightline_ _ _
            (Binop (LvMem (Indir Sp 4)) Rv Minus (length (funcVars f))
              :: nil))
          (statementCmd (funcVars f) H _ (optimizer (Body f)) Syntax.Skip))
        (Seq_ H
          (Straightline_ _ _
            (Assign Rp (LvMem (Indir Sp 0))
              :: nil))
          (IGoto _ _ Rp)))).

  Definition compileFunc (f : func) : StructuredModule.function modName :=
    (Name f, funcSpec f, funcBody f).

  Variable functions : list func.

  Definition imports : list import :=
    ("my_malloc", "malloc", Precondition my_mallocS None)
    :: ("my_free", "free", Precondition my_freeS None)
    :: nil.

  Definition compile : module := StructuredModule.bmodule_ imports (map compileFunc functions).

  Hypothesis Names_NoDup : NoDup (map Name functions).

  Lemma goodNames : forall funcs m,
    NoDup (map Name funcs)
    -> List.Forall (fun f => forall l, ~LabelMap.In (Name f, l) m) funcs
    -> match (List.fold_left (fun mOpt p => let '(modl, _, _) := p in
      match mOpt with
        | None => None
        | Some m => let k := (modl, Local 0) in
          if LabelMap.mem k m then None
            else Some (LabelMap.add k tt m)
      end) (map compileFunc funcs) (Some m)) with
         | None => False
         | Some _ => True
       end.
    induction funcs; simpl; intuition;
      match goal with
        | [ H : List.Forall _ (_ :: _) |- _ ] => inversion H; clear H; subst
      end;
      match goal with
        | [ H : NoDup (_ :: _) |- _ ] => inversion H; clear H; subst
      end.
    case_eq (LabelMap.mem (Name a, Local 0) m); intros.
    apply LabelMap.mem_2 in H; exfalso; eauto.
    apply IHfuncs; auto.
    eapply Forall_forall; intros.
    eapply Forall_forall in H4; [ | eassumption ].
    apply LabelFacts.add_in_iff in H1; intuition; [ | eauto ].
    injection H6; clear H6; intros; subst.
    rewrite H6 in *.
    eapply in_map in H0; eauto.
  Qed.

  Hint Extern 1 => apply goodNames.

  Lemma notInEmpty : forall A funcs,
    List.Forall (fun f => forall l, ~LabelMap.In (Name f, l) (@LabelMap.empty A)) funcs.
    intros; apply Forall_forall; intuition.
    apply LabelFacts.empty_in_iff in H0; tauto.
  Qed.

  Hint Immediate notInEmpty.

  Lemma importsIntact' : forall l (funcs : list func) imap,
    fst l <> modName
    -> (forall k, LabelMap.In k imap -> fst l <> modName)
    -> LabelMap.find (elt:=assert) l (List.fold_left (fun m p => let '(f, pre, _) := p in
      LabelMap.add (modName, Global f) pre m) (map compileFunc funcs) imap)
    = LabelMap.find (elt:=assert) l imap.
    induction funcs; simpl; intuition.
    rewrite IHfuncs; auto.
    apply LabelFacts.add_neq_o.
    destruct l; simpl in *; congruence.
  Qed.

  Lemma importsIntact : forall l,
    fst l <> modName
    -> LabelMap.find (elt:=assert) l (fullImports imports (map compileFunc functions))
    = LabelMap.find (elt:=assert) l (importsMap imports).
    intros; apply importsIntact'; auto.
  Qed.

  Hint Extern 1 => apply importsIntact; discriminate.

  Require Import Wrap.

  Ltac clear_fancier :=
    clear_fancy;
    repeat match goal with
             | [ H : context[Name] |- _ ] => clear H
             | [ H : Safety.Safe _ _ _ |- _ ] => clear H
             | [ H : List.Forall _ _ |- _ ] => clear H
           end.

  Import Ascii.

  Definition goodVar (x : string) : Prop :=
    match x with
      | String "!"%char _ => False
      | String "."%char _ => False
      | String "_"%char _ => False
      | "rp" => False
      | _ => True
    end.

  Record goodFunc (f : func) : Prop := {
    FewEnoughVars : goodSize (length (funcVars f) + MIN_RESERVED);
    NoDups : NoDup (Vars f);
    GoodNames : List.Forall goodVar (Vars f);
    WellScoped : incl (SemanticsLemmas.footprint (Body f)) ("__arg" :: Vars f);
    NoUninitializedSafe : forall fs vs a, Safety.Safe fs (Body f) (vs, a)
      -> forall vs', sel vs' "__arg" = sel vs "__arg"
        -> Safety.Safe fs (Body f) (vs', a);
    NoUninitializedRunsTo : forall fs vs a vs' a', RunsTo fs (Body f) (vs, a) (vs', a')
      -> forall vs'', sel vs'' "__arg" = sel vs "__arg"
        -> exists vs''', RunsTo fs (Body f) (vs'', a) (vs''', a')
  }.

  Lemma In_tempChunk : forall x d base,
    In x (tempChunk base d)
    -> match x with
         | String "."%char _ => True
         | String "!"%char _ => True
         | _ => False
       end.
    induction d; simpl; intuition.
    apply in_app_or in H; simpl in *; intuition.
    apply IHd in H0; auto.
    destruct (base + d); simpl in *; subst; tauto.
  Qed.

  Lemma NoDup_app : forall A (ls2 ls1 : list A),
    NoDup ls1
    -> NoDup ls2
    -> (forall x, In x ls1 -> ~In x ls2)
    -> NoDup (ls1 ++ ls2).
    induction 1; simpl; intuition.
    constructor.
    intro.
    apply in_app_or in H4; intuition eauto.
    eauto.
  Qed.

  Lemma NoDup_tempChunk : forall d base,
    NoDup (tempChunk base d).
    induction d; simpl; intuition.
    apply NoDup_app.
    auto.
    constructor.
    simpl; intuition.
    constructor.
    simpl; intuition; subst.
    apply temp_in_chunk_offset in H; destruct H; intuition.
    apply tempOf_inj in H1.
    omega.
  Qed.    

  Lemma goodFunc_NoDup : forall f,
    goodFunc f
    -> NoDup ("rp" :: "__reserved" :: "__arg" :: funcVars f).
    unfold funcVars; intros.

    constructor.
    simpl; intuition.
    apply in_app_or in H0; intuition.
    eapply Forall_forall in H1.
    2: apply GoodNames; auto.
    tauto.
    apply In_tempChunk in H1; tauto.

    constructor.
    simpl; intuition.
    apply in_app_or in H1; intuition.
    eapply Forall_forall in H0.
    2: apply GoodNames; auto.
    tauto.
    apply In_tempChunk in H0; tauto.

    constructor.
    simpl; intuition.
    apply in_app_or in H0; intuition.
    eapply Forall_forall in H1.
    2: apply GoodNames; auto.
    tauto.
    apply In_tempChunk in H1; tauto.

    apply NoDup_app.
    apply NoDups; auto.

    apply NoDup_tempChunk.

    intuition.
    eapply Forall_forall in H0; [ | apply GoodNames; auto ].
    apply temp_in_chunk_offset in H1.
    destruct H1; intuition; subst; simpl in *.
    destruct x0; tauto.
  Qed.

  Hint Immediate goodFunc_NoDup.

  Lemma optimizer_footprint : forall s, List.incl (SemanticsLemmas.footprint (optimizer s)) (SemanticsLemmas.footprint s).
    unfold is_good_optimizer in *; intuition.
  Qed.

  Lemma optimizer_depth : forall s, depth (optimizer s) <= depth s.
    unfold is_good_optimizer in *; intuition.
  Qed.
  Hint Resolve optimizer_depth.

  Lemma optimizer_is_backward_simulation : forall fs s v vs' heap', RunsTo fs (optimizer s) v (vs', heap') -> exists vs'', RunsTo fs s v (vs'', heap').
    unfold is_good_optimizer in *; intuition.
  Qed.

  Lemma optimizer_is_safety_preservation : forall fs s v, Safety.Safe fs s v -> Safety.Safe fs (optimizer s) v.
    unfold is_good_optimizer in *; intuition.
  Qed.

  Lemma goodVcs : forall funcs,
    List.Forall goodFunc funcs
    -> NoDup (map Name funcs)
    -> vcs (makeVcs imports (map compileFunc functions) (map compileFunc funcs)).
  Proof.
    clear optimizer_is_good_optimizer.
    induction 1; simpl; intuition;
      match goal with
        | [ H : NoDup (_ :: _) |- _ ] => inversion H; clear H; subst
      end; wrap0; clear_fancier.

    sep_auto.
    sep_auto.
    sep_auto.
    hnf; post.
    match goal with
      | [ H : Safety.Safe _ _ _ |- _ ] =>
        generalize dependent H; evaluate auto_ext; intro
    end.
    destruct x0; fold (@length string) in *; simpl in *.
    change (locals ("rp" :: "__reserved" :: "__arg" :: nil)
      (upd (upd x5 "rp" (Regs x2 Rp)) "__reserved"
        (sel x5 "__reserved"
          ^- natToW (Datatypes.length (funcVars x))))
      x7 (Regs x2 Sp))
      with (locals_in ("rp" :: "__reserved" :: "__arg" :: nil)
        (upd (upd x5 "rp" (Regs x2 Rp)) "__reserved"
          (sel x5 "__reserved"
            ^- natToW (Datatypes.length (funcVars x))))
        x7 (Regs x2 Sp)
        (funcVars x) ("rp" :: "__reserved" :: "__arg" :: funcVars x) (x7 - length (funcVars x))) in *.
    assert (ok_in ("rp" :: "__reserved" :: "__arg" :: nil) x7
      (funcVars x) ("rp" :: "__reserved" :: "__arg" :: funcVars x) (x7 - length (funcVars x))).
    hnf; simpl; intuition.
    generalize (FewEnoughVars _ H); intros; nomega.
    match goal with
      | [ H : Safety.Safe _ _ _ |- _ ] =>
        generalize dependent H; evaluate auto_ext; intro
    end.
    fold (@length string) in *; simpl in *.
    descend.
    eauto.
    eauto.
    instantiate (2 := (_, _)); simpl.
    clear H13; step auto_ext.
    fold (@length string); descend.
    subst.
    generalize (FewEnoughVars _ H); intro.
    rewrite wordToNat_wminus.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize (length (funcVars x))).
    eapply goodSize_weaken; [ eapply FewEnoughVars; eauto | omega ].
    pre_nomega.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize (length (funcVars x))).
    eapply goodSize_weaken; [ eapply FewEnoughVars; eauto | omega ].
    fold (@length string); descend.
    generalize (FewEnoughVars _ H); intro.
    nomega.
    fold (@length string); descend.
    constructor; [ | intros; constructor ].
    eapply optimizer_is_safety_preservation.
    eapply NoUninitializedSafe; eauto.
    step auto_ext.
    step auto_ext.
    descend; step auto_ext.
    fold (@length string).
    instantiate (1 := snd x10).
    instantiate (1 := fst x10).
    change (locals ("rp" :: "__reserved" :: "__arg" :: nil) (fst x10) x7 (Regs x9 Sp))
      with (locals_out ("rp" :: "__reserved" :: "__arg" :: nil) (fst x10) x7 (Regs x9 Sp)
        (funcVars x) ("rp" :: "__reserved" :: "__arg" :: funcVars x) (x7 - length (funcVars x))).
    assert (ok_out ("rp" :: "__reserved" :: "__arg" :: nil) x7
      (funcVars x) ("rp" :: "__reserved" :: "__arg" :: funcVars x) (x7 - length (funcVars x))).
    hnf; intuition idtac.
    generalize (FewEnoughVars _ H); intro; nomega.
    generalize H17.
    repeat match goal with
             | [ H : _ |- _ ] => clear H
           end.
    intro; step auto_ext.
    destruct H15; simpl in *; intuition idtac.
    inversion H17; clear H17; subst.
    inversion H24; clear H24; subst.
    destruct x11; simpl in *; subst.
    eapply optimizer_is_backward_simulation in H21.
    openhyp.
    eauto using NoUninitializedRunsTo.

    hnf; simpl; intuition (try rewrite app_nil_r).

    specialize (WellScoped _ H); simpl.
    unfold incl; intros.
    eapply optimizer_footprint in H1.
    apply H0 in H1; simpl in *; intuition.
    unfold funcVars; eauto.

    rewrite Max.max_0_r.
    apply incl_appr; auto.

    hnf; intuition.
    eapply optimizer_footprint in H0.
    apply WellScoped in H0; auto.
    simpl in *; intuition; subst.
    apply In_tempChunk in H1; tauto.
    eapply Forall_forall in H2; [ | eapply GoodNames; eauto ].
    apply temp_in_chunk_offset in H1.
    destruct H1; intuition subst; simpl in *.
    destruct x0; tauto.

    apply in_app_or in H0; intuition.
    eapply Forall_forall in H1; [ | eapply GoodNames; eauto ].
    tauto.

    apply temp_in_chunk_offset in H1.
    destruct H1; intuition subst; simpl in *.
    destruct x0; discriminate.

    apply in_app_or in H0; intuition.
    eapply Forall_forall in H1; [ | eapply GoodNames; eauto ].
    tauto.

    apply temp_in_chunk_offset in H1.
    destruct H1; intuition subst; simpl in *.
    destruct x0; discriminate.

    apply in_app_or in H0; intuition.
    eapply Forall_forall in H1; [ | eapply GoodNames; eauto ].
    tauto.

    apply temp_in_chunk_offset in H1.
    destruct H1; intuition subst; simpl in *.
    destruct x0; discriminate.

    post.
    assert (In "rp" ("rp" :: "__reserved" :: "__arg" :: funcVars x)) by (simpl; tauto).
    change (Indir Sp 0)
      with (Indir Sp (variablePosition ("rp" :: "__reserved" :: "__arg" :: funcVars x) "rp")) in *.
    evaluate auto_ext.

    post.
    assert (In "rp" ("rp" :: "__reserved" :: "__arg" :: funcVars x)) by (simpl; tauto).
    change (Indir Sp 0)
      with (Indir Sp (variablePosition ("rp" :: "__reserved" :: "__arg" :: funcVars x) "rp")) in *.
    evaluate auto_ext.
    destruct x3; simpl in *.
    repeat match goal with
             | [ H : _ \/ _ |- _ ] => clear H
           end.
    descend.
    step auto_ext.
    step auto_ext.
    descend.
    instantiate (1 := (_, _)); simpl.
    step auto_ext.
    eauto.
  Qed.

  Hint Immediate goodVcs.

  Theorem compileOk : List.Forall goodFunc functions
    -> NoDup (map Name functions)
    -> moduleOk compile.
    intros; apply StructuredModule.bmoduleOk; auto.
  Qed.
End Compiler.
