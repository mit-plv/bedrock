(** Compiling the deeply embedded programming language *)

Require Import AutoSep Wrap Malloc.

Require Import Depl.Logic Depl.Cancel Depl.AlgebraicDatatypes Depl.Statements.


(** * Lowering DEPL expressions to Bedrock SPS expressions *)

Definition exprC (e : expr) : rvalue' :=
  match e with
    | Var x => x
    | Const w => w
  end.
(** The above looks like a bit of magic.  It's all in the coercions (from main Bedrock library). *)

Theorem exprC_correct : forall specs P stn st xs V vs fE e e' res fvs,
  vars_ok fE V vs
  -> exprD vs e = Some e'
  -> exprV xs e
  -> ~In "rp" xs
  -> interp specs (![locals ("rp" :: xs) V res (Regs st Sp) * P] (stn, st))
  -> (forall x e0, vs x = Some e0
    -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e0 fE1 = Logic.exprD e0 fE2)
  -> exists w,
    evalRvalue stn st (exprC e xs) = Some w
    /\ Logic.exprD e' fE = Dyn w
    /\ (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e' fE1 = Logic.exprD e' fE2).
Proof.
  destruct e; simpl; intuition.

  injection H0; clear H0; intros; subst; eauto.

  assert (Hnone : evalInstrs stn st (IL.Assign Rv (variableSlot x xs) :: nil) <> None).
  simp.
  generalize dependent H0.
  evaluate auto_ext.

  assert (Hsome : forall st', evalInstrs stn st (IL.Assign Rv (variableSlot x xs) :: nil) = Some st'
    -> Regs st' Rv = sel V x).
  simp.
  generalize dependent H0.
  evaluate auto_ext; auto.

  Transparent evalInstrs.
  simpl in *.
  Opaque evalInstrs.
  match goal with
    | [ |- exists x, ?X = _ /\ _ ] => destruct X; try tauto
  end.
  specialize (Hsome _ eq_refl); simpl in *.
  rewrite rupd_eq in Hsome; subst.
  eauto 10.
Qed.

Theorem exprC_hygienic : forall xs vs e e' fvs,
  exprD vs e = Some e'
  -> exprV xs e
  -> ~In "rp" xs
  -> (forall x e0, vs x = Some e0
    -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e0 fE1 = Logic.exprD e0 fE2)
  -> (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e' fE1 = Logic.exprD e' fE2).
Proof.
  destruct e; simpl; intuition eauto.

  injection H; clear H; intros; subst; eauto.
Qed.


(** * Lowering statements *)

Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
  Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).
Local Infix ";;" := SimpleSeq : SP_scope.

Fixpoint locateCon' (n : nat) (s : string) (cs : list ncon) : option (nat * ncon) :=
  match cs with
    | nil => None
    | c :: cs' => if string_eq s (NName c) then Some (n, c)
      else locateCon' (S n) s cs'
  end.

Fixpoint locateCon (s : string) (dts : list ndatatype) : option (string * nat * ncon) :=
  match dts with
    | nil => None
    | dt :: dts' =>
      match locateCon' O s (snd dt) with
        | None => locateCon s dts'
        | Some (n, c) => Some (fst dt, n, c)
      end
  end.

(** Version of [Logic.predD] specialized to predicates with no free higher-order variables *)
Definition predD (p : pred) (fE : fo_env) : HProp :=
  predD p (fun _ _ => Emp)%Sep fE.
Definition normalD (p : normal) (fE : fo_env) : HProp :=
  normalD p (fun _ _ => Emp)%Sep fE.

(** Generic precondition of a statement, translated to base Bedrock from Depl-speak *)
Definition precond (vs : vars) (pre post : normal) :=
  (* First, quantify over a context assigning values to specification variables. *)
  Al fE,
    (* Naturally, we rely on the malloc() data structures being around. *)
    PRE[V] mallocHeap 0
      (* We also need the Depl precondition, of course. *)
      * normalD pre fE
      (* Finally, the symbolic variable valuation should be accurate. *)
      * [| vars_ok fE V vs |]
    POST[R] mallocHeap 0
      (* The postcondition holds, in an [fo_env] that lets it mention the return value. *)
      * normalD post (fo_set fE "result" (Dyn R)).

(** Evaluate the arguments to a constructor, saving results in a record in memory. *)
Fixpoint initArgs (args : list expr) (base : fo_var) (pos : nat) : chunk :=
  match args with
  | nil => Skip
  | arg :: args =>
    base + (4 * pos)%nat *<- exprC arg;;
    initArgs args base (S pos)
  end%SP.

Section ForallF.
  Variable A : Type.
  Variables P Q : A -> Prop.

  Hypothesis P_Q : forall x, P x -> Q x.

  Theorem ForallF_weaken : forall ls,
    ForallF P ls -> ForallF Q ls.
  Proof.
    induction ls; simpl; intuition.
  Qed.
End ForallF.

Record nconWf (nc : ncon) := {
  EnoughArgs : (length (NRecursive nc) + length (NNonrecursive nc) >= 1)%nat;
  NotTooManyArgs : goodSize (S (length (NRecursive nc) + length (NNonrecursive nc)))
}.

Definition ndatatypeWf (nd : ndatatype) :=
  List.Forall nconWf (snd nd).

Definition ndatatypesWf := List.Forall ndatatypeWf.

Local Notation "l ~~ im ~~> s" := (LabelMap.find l%SP im = Some (Programming.Precondition s None)) (at level 0).

Section stmtC.
  Variable dts : list ndatatype.
  Variable Hdts : ndatatypesWf dts.

  Fixpoint stmtC (vs : vars) (fvs : list fo_var)
    (pre post : normal) (nextDt : string) (s : stmt)
    (k : vars -> list fo_var -> normal -> normal -> string -> chunk) : chunk :=
    match s with
      | Assign x e =>
        match exprD vs e with
          | None => Fail
          | Some e' => x <- exprC e;; k (vars_set vs x e') fvs pre post nextDt
        end
      | Seq s1 s2 => stmtC vs fvs pre post nextDt s1
        (fun vs' fvs' pre' post' nextDt' =>
          stmtC vs' fvs' pre' post' nextDt' s2 k)
      | Ret e => Return (exprC e)
      | Allocate x conName args =>
        match locateCon conName dts with
          | None => Fail
          | Some (dtName, tag, c) =>
            match exprsD vs args with
              | None => Fail
              | Some args' =>
                match cancel fvs ("this" :: nil)
                  pre (allocatePre dtName c args') with
                  | Failure _ => Fail
                  | Success s lhs P =>
                    match s "this" with
                      | None => Fail
                      | Some model =>
                        let vs' := vars_set vs x (Logic.Var nextDt) in
                        let pre' := {| NQuants := NQuants pre;
                          NPure := NPure pre;
                          NImpure := Named dtName (model :: Logic.Var nextDt
                            :: nil) :: lhs |} in
                        "_" <-- Call "malloc"!"malloc"(0, S (length args))
                        [Al fE, Al ws,
                          PRE[V, R] array ws R * [| length ws = S (length args) |]
                            * [| R <> 0 |] * [| freeable R (S (length args)) |]
                            * mallocHeap 0 * normalD pre fE * [| vars_ok fE V vs |]
                          POST[R'] mallocHeap 0 * normalD post (fo_set fE "result" (Dyn R'))];;
                        "_" *<- tag;;
                        initArgs args "_" 1;;
                        x <- "_";;
                        k vs' (nextDt :: fvs) pre' post (nextDt ++ "'")%string
                    end
                end
            end
        end
    end%SP.


  (** * Key lemmas to pass to Wrap *)

  Lemma vars_ok_sel : forall fE V vs,
    vars_ok fE (sel V) vs = vars_ok fE V vs.
  Proof.
    auto.
  Qed.

  Hint Rewrite vars_ok_sel.

  (* Use a hypothesis telling us an expanded form implied by the known precondition. *)
  Ltac pre_implies :=
    match goal with
      | [ H : interp _ _, H' : forall specs0 : codeSpec _ _, _ |- _ ] =>
        apply H' in H; clear H'; post; intuition idtac; autorewrite with core in *
    end.

  Ltac rewriteall :=
    repeat match goal with
             | [ H : _ |- _ ] => rewrite H in *
           end.

  (* Case-split on an [option] being [match]ed in conclusion. *)
  Ltac case_option :=
    match goal with
      | [ |- context[match ?E with None => _ | _ => _ end] ] =>
        match E with
          | context[match _ with None => _ | _ => _ end] => fail 1
          | _ => case_eq E; post
        end
      | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
        match E with
          | context[match _ with None => _ | _ => _ end] => fail 1
          | _ => case_eq E; post; rewriteall
        end
      | [ _ : context[if in_dec string_dec ?x ?y then _ else _] |- _ ] =>
        destruct (in_dec string_dec x y); post
    end; autorewrite with core in *.

  (* Use [evaluate] to get pure facts in a precondition into the normal proof context. *)
  Ltac pre_evalu :=
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => generalize dependent H
             | [ H : _ _ = Some _ |- _ ] => generalize dependent H
             | [ H : _ _ = None |- _ ] => generalize dependent H
             | [ H : _ _ = None -> False |- _ ] => generalize dependent H
             | [ x : _ -> option Logic.expr |- _ ] => change vars in x
             | [ x : vars -> _ |- _ ] => generalize dependent x
             | [ H : importsGlobal _ |- _ ] => generalize dependent H; clear dependent H
             | [ H : LabelMap.find _ _ = Some _ |- _ ] => clear H
             | [ H : ForallF _ _ |- _ ] => generalize dependent H
           end;
    try match goal with
          | [ _ : interp _ (![_] (fst ?st, _)) |- _ ] =>
            destruct st; simpl in *
        end; clear_fancy; evaluate auto_ext; intros.

  (* Clear hypotheses that will confuse Bedrock automation. *)
  Ltac cancl_clear :=
    repeat match goal with
             | [ H : importsGlobal _ |- _ ] => clear dependent H
             | [ H : _ _ = Some _ |- _ ] => clear H
             | [ H : _ _ = None |- _ ] => clear H
             | [ H : (_ _ <> None)%type |- _ ] => clear H
             | [ H : _ _ = None -> False |- _ ] => clear H
             | [ H : stmtD _ _ _ _ _ |- _ ] => clear H
             | [ H : LabelMap.find _ _ = Some _ |- _ ] => clear H
             | [ H : ForallF _ _ |- _ ] => clear H
           end.

  (* Use separation logic entailment from a hypothesis to conclusion. *)
  Ltac cancl :=
    match goal with
      | [ _ : interp ?specs1 (![_] (?s1, ?x1)) |- interp ?specs2 (![_] (?s2, ?x2)) ] =>
        equate specs1 specs2; equate s1 s2; equate x1 x2;
        cancl_clear; cancel auto_ext
      | [ _ : interp ?specs (![_] ?s) |- interp ?specs (![_] ?s) ] =>
        cancl_clear; cancel auto_ext
      | [ |- interp _  (![_]%PropX _ ---> ![_]%PropX _) ] => cancl_clear; cancel auto_ext
    end.

  (* Apply the [exprC_correct] lemma, using cancelation to prove one of its premises. *)
  Ltac exprC_correct :=
    match goal with
      | [ H : exprD _ _ = Some _ |- _ ] => eapply exprC_correct in H; try cancl; eauto;
        try match goal with
              | [ H : exists x, _ /\ _ |- _ ] => destruct H as [ ? [ ? [ ] ] ]
            end
    end.

  Lemma determine_rvalue : forall stn st lv rv st' w is,
    evalInstrs stn st (IL.Assign lv rv :: is) = st'
    -> evalRvalue stn st rv = Some w
    -> evalInstrs stn st (IL.Assign lv w :: is) = st'.
  Proof.
    Transparent evalInstrs.
    simpl; intros.
    rewrite H0 in *; auto.
    Opaque evalInstrs.
  Qed.

  (* Use a previous conclusion of [exprC_correct] to simplify an [evalInstrs] hypothesis. *)
  Ltac determine_rvalue :=
    match goal with
      | [ H1 : evalInstrs _ _ _ = _, H2 : evalRvalue _ _ _ = Some _ |- _ ] =>
        eapply determine_rvalue in H1; [ clear H2 | exact H2 ]
    end.

  (* Full symbolic evaluation *)
  Ltac evalu :=
    try determine_rvalue;
      try match goal with
            | [ H : In _ _, H' : forall x, In x _ -> In x _ |- _ ] =>
              apply H' in H
          end; simp;
      repeat match goal with
               | [ H : _ _ = Some _ |- _ ] => generalize dependent H
               | [ H : _ _ = None |- _ ] => generalize dependent H
               | [ H : _ _ = None -> False |- _ ] => generalize dependent H
               | [ H : importsGlobal _ |- _ ] => generalize dependent H; clear dependent H
               | [ H : ForallF _ _ |- _ ] => generalize dependent H
             end; clear_fancy;
    (* Extra simplification for function return *)
    try match goal with
          | [ _ : context[locals ("rp" :: ?ns) _ _ _], H : context[natToW 0] |- _ ] =>
            assert (In "rp" ("rp" :: ns)) by (simpl; tauto);
              change (natToW 0) with (natToW (variablePosition ("rp" :: ns) "rp")) in H
        end;
    evaluate auto_ext; intros.

  Ltac my_descend := descend; autorewrite with core in *.
  Hint Rewrite sel_upd_ne using (intro; subst; tauto).

  Lemma string_eq_complete : forall s1 s2,
    if string_eq s1 s2 then s1 = s2 else s1 <> s2.
  Proof.
    intros; destruct (string_dec s1 s2); subst.
    rewrite string_eq_true; auto.
    rewrite string_eq_false; auto.
  Qed.

  Lemma vars_ok_upd : forall fE V vs x w e,
    vars_ok fE V vs
    -> Logic.exprD e fE = Dyn w
    -> vars_ok fE (upd V x w) (vars_set vs x e).
  Proof.
    unfold vars_ok, sel, upd, vars_set; intros.
    generalize (string_eq_complete x0 x).
    destruct (string_eq x0 x), (string_dec x0 x); intuition.
  Qed.

  Local Hint Resolve vars_ok_upd.

  Lemma exprV_weaken : forall xs xs',
    (forall x, In x xs -> In x xs')
    -> forall e, exprV xs e -> exprV xs' e.
  Proof.
    destruct e; simpl; intuition.
  Qed.

  Local Hint Resolve exprV_weaken.

  Lemma stmtV_weaken : forall xs xs',
    (forall x, In x xs -> In x xs')
    -> forall s, stmtV dts xs s -> stmtV dts xs' s.
  Proof.
    induction s; simpl; intuition eauto using ForallF_weaken.
  Qed.

  Local Hint Resolve stmtV_weaken.

  Lemma vars_set_contra : forall vs x v x' v',
    vars_set vs x v x' = None
    -> vs x = Some v'
    -> (vs x' = None -> False)
    -> False.
  Proof.
    unfold vars_set; intros;
      destruct (string_dec x' x); subst; eauto; discriminate.
  Qed.

  Local Hint Resolve vars_set_contra.

  (* VC generation uses some empty marker predicates to indicate failure.
   * Try to find one to invert on, proving the goal trivially. *)
  Ltac use_error_message :=
    match goal with
      | [ H : bad_assignment_lhs _ |- _ ] => inversion H
      | [ H : bad_assignment_rhs _ |- _ ] => inversion H
    end.

  Lemma addQuants_Emp : forall G (S : subs _ _ G) qs fE,
    SubstsH S (addQuants qs (fun _ : fo_env => Emp) fE) ===> Emp.
  Proof.
    induction qs; simpl; intros; Himp.

    apply Himp_refl.

    apply Himp'_ex; auto.
  Qed.

  Theorem sentail_sound : forall fvs fE S lhs rhs P,
    sentail fvs lhs rhs = ProveThis P
    -> P
    -> List.Forall (wellScoped (NQuants rhs ++ fvs)) (NImpure rhs)
    -> (forall x, In x fvs -> ~In x (NQuants lhs))
    -> SubstsH S (normalD lhs fE)
    ===> SubstsH S (normalD rhs fE).
  Proof.
    unfold sentail; intros.
    case_eq (cancel fvs nil lhs rhs); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    destruct NewLhs; try discriminate.
    injection H; clear H; intros; subst.
    assert (Heasy : forall x, In x fvs -> ~In x nil) by (simpl; tauto).
    specialize (cancel_sound fvs nil fE nil (fun _ _ => Emp%Sep) S _ _ _ _ _ Heasy H3 H0 H1).
    unfold Logic.normalD at 3; simpl.
    intros.
    unfold normalD.
    eapply Himp_trans; try apply H; clear H; auto.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | ] | ].
    apply addQuants_Emp.
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_Emp.
  Qed.

  Lemma use_hygiene : forall fvs vs x x' e0 e2 fE1 fE2,
    (forall x e, vs x = Some e
      -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
        -> Logic.exprD e fE1 = Logic.exprD e fE2)
    -> (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
      -> Logic.exprD e0 fE1 = Logic.exprD e0 fE2)
    -> vars_set vs x e0 x' = Some e2
    -> (forall y, In y fvs -> fE1 y = fE2 y)
    -> Logic.exprD e2 fE1 = Logic.exprD e2 fE2.
  Proof.
    unfold vars_set; intros.
    destruct (string_dec x' x); subst; eauto.
    injection H1; clear H1; intros; subst; eauto.
  Qed.

  Hint Immediate use_hygiene.

  (* Prove we never run off the end of a function.
   * We're in CPS, so all postconditions should be contradictory. *)
  Theorem stmtC_post : forall im mn (H : importsGlobal im) ns res s k,
    (forall specs st vs fvs pre post nextDt pre0,
       interp specs (Structured.Postcondition (toCmd (k vs fvs pre post nextDt)
                                                     mn H ns res pre0) st)
       -> False)
    -> (forall specs st vs fvs pre post nextDt pre0,
       interp specs (Structured.Postcondition (toCmd (stmtC vs fvs pre post nextDt s k)
                                                     mn H ns res pre0) st)
       -> False).
  Proof.
    induction s; simpl; intuition idtac;
      repeat match goal with
               | [ _ : context[match ?E with _ => _ end] |- _ ] =>
                 destruct E; simpl in *; eauto
               | [ IH : forall k : _ -> _, _, H : interp _ (Structured.Postcondition _ _) |- _ ] =>
                 apply IH in H; clear IH; intuition idtac
               | [ H : interp _ [| False |]%PropX |- _ ] => propxFo
               | [ x : (_ * _)%type |- _ ] => destruct x
             end.
  Qed.

  Definition normalWf' := normalWf.

  Definition scopey fvs post := List.Forall (wellScoped (NQuants post ++ "result" :: fvs)).
  Definition scopey' x := List.Forall (fun p => exists bvs, boundVars p = Some bvs /\ ~In x bvs).

  Theorem nsubst_bwd : forall x e fvs n fE,
    normalWf fvs n
    -> fE x = Logic.exprD e fE
    -> (forall y, In y fvs -> ~In y (NQuants n))
    -> (forall fE1 fE2, (forall x, In x fvs -> fE1 x = fE2 x)
      -> Logic.exprD e fE1 = Logic.exprD e fE2)
    -> In x fvs
    -> normalD (nsubst x e n) fE ===> normalD n fE.
  Proof.
    intros.
    change (normalD (nsubst x e n) fE) with (SubstsH (SNil _ _) (normalD (nsubst x e n) fE)).
    change (normalD n fE) with (SubstsH (SNil _ _) (normalD n fE)).
    eapply nsubst_bwd; eauto.
  Qed.

  Section chunk_params.
    Variable im : LabelMap.t assert.
    Variable mn : string.
    Variable H : importsGlobal im.
    Variable ns : list string.
    Variable res : nat.
    Variable xs : list string.

    Hypothesis Hres : (res >= 7)%nat.
    Hypothesis Hmalloc : "malloc"!"malloc" ~~ im ~~> Malloc.mallocS.
    Hypothesis H0 : ~In "rp" ns.
    Hypothesis H1 : forall x, In x xs -> In x ns.
    Hypothesis H_ : In "_" ns.
    Hypothesis H_not : ~In "_" xs.

    Lemma initArgs_vc : forall vs fvs base,
      ~In "result" fvs
      -> (forall x e, vs x = Some e
        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
          -> Logic.exprD e fE1 = Logic.exprD e fE2)
      -> In base ns
      -> forall args pos pre0 ws',
           exprsD vs args = Some ws'
           -> ForallF (exprV ns) args
           -> (forall specs st,
            interp specs (pre0 st)
            -> exists fE V ws F,
                 interp specs (![ locals ("rp" :: ns) V res st#Sp * array ws (sel V base)
                                  * [| vars_ok fE V vs |] * F ] st)
                 /\ length ws = pos + length args)
        -> vcs (VerifCond (toCmd (initArgs args base pos) mn H ns res pre0)).
    Proof.
      Opaque mult.
      induction args; wrap0.

      pre_implies.
      case_option; try discriminate.
      case_option; try discriminate.
      injection H5; clear H5; intros; subst.
      pre_evalu.
      exprC_correct.
      unfold lvalIn in *.
      prep_locals.
      change (Binop (regInL Rv ns) (LvMem (Sp + variablePosition ("rp" :: ns) base)%loc)
                    Plus (immInR (4 * pos) ns) :: IL.Assign (LvMem Rv) (exprC a ns) :: nil)
             with ((Binop (regInL Rv ns) (LvMem (Sp + variablePosition ("rp" :: ns) base)%loc)
                         Plus (immInR (4 * pos) ns) :: nil) ++ (IL.Assign (LvMem Rv) (exprC a ns) :: nil)) in H5.
      apply evalInstrs_app_fwd_None in H5.
      unfold regInL, immInR in *.
      destruct H5 as [ | [ ? [ ] ] ].
      clear dependent H.
      clear H11 H6.
      evaluate auto_ext.
      assert (natToW pos < natToW (length x1)).
      apply lt_goodSize; eauto.
      apply goodSize_weaken with (length x1); eauto.

      clear dependent H.
      rewrite Mult.mult_comm in H5.
      rewrite natToW_times4 in H5.
      rewrite wmult_comm in H5.

      Lemma exprC_uses : forall e ns stn st1 st2,
        Mem st1 = Mem st2
        -> Regs st1 Sp = Regs st2 Sp
        -> evalRvalue stn st1 (exprC e ns) = evalRvalue stn st2 (exprC e ns).
      Proof.
        destruct e; simpl; intuition.
      Qed.

      erewrite exprC_uses in H6.
      determine_rvalue.
      clear H11.
      move H5 after H16.
      evaluate auto_ext.
      Transparent evalInstrs.
      simpl in H5.
      match type of H5 with
        | match match ?E with _ => _ end with _ => _ end = _ => destruct E
      end.
      injection H5; intros; subst; auto.
      discriminate.
      simpl in H5.
      match type of H5 with
        | match match ?E with _ => _ end with _ => _ end = _ => destruct E
      end.
      injection H5; intros; subst; auto.
      discriminate.
      Opaque evalInstrs.

      simpl in *; intuition idtac.
      case_option; try discriminate.
      case_option; try discriminate.
      injection H5; clear H5; intros; subst.

      Lemma exprD_exprD : forall fE V vs e e',
        exprD vs e = Some e'
        -> vars_ok fE V vs
        -> exists w : W, Logic.exprD e' fE = Dyn w.
      Proof.
        destruct e; simpl; intuition.
        injection H2; clear H2; intros; subst.
        simpl; eauto.
        hnf in H3; eauto.
      Qed.

      eapply IHargs; eauto.
      post.
      pre_implies.
      pre_evalu.
      unfold lvalIn in *.
      prep_locals.
      generalize H6; intro HexprD.
      eapply exprD_exprD in HexprD; eauto.
      destruct HexprD.
      change (Binop (regInL Rv ns) (LvMem (Sp + variablePosition ("rp" :: ns) base)%loc)
                    Plus (immInR (4 * pos) ns) :: IL.Assign (LvMem Rv) (exprC a ns) :: nil)
             with ((Binop (regInL Rv ns) (LvMem (Sp + variablePosition ("rp" :: ns) base)%loc)
                         Plus (immInR (4 * pos) ns) :: nil) ++ (IL.Assign (LvMem Rv) (exprC a ns) :: nil)) in H12.
      apply evalInstrs_app_fwd in H12.
      destruct H12; intuition idtac.
      unfold regInL, immInR in *.
      clear dependent H.
      rewrite Mult.mult_comm in H15.
      rewrite natToW_times4 in H15.
      rewrite wmult_comm in H15.
      eapply exprC_correct in H6.
      2: eauto.
      2: eauto.
      2: eauto.
      Focus 2.
      instantiate (3 := (array x2 (sel x1 base) * x3)%Sep).
      instantiate (1 := x).
      instantiate (1 := s).
      instantiate (1 := res).
      instantiate (1 := specs).
      generalize H9; clear; intros.
      step auto_ext.
      2: eauto.
      destruct H6; intuition idtac.
      erewrite exprC_uses in H6.
      determine_rvalue.
      clear H5.
      move H15 after H16.
      assert (natToW pos < natToW (length x2)).
      apply lt_goodSize; eauto.
      apply goodSize_weaken with (length x2); eauto.

      rewrite H14 in H.
      injection H; intro Hinj.
      Require Import Eqdep.
      apply inj_pair2 in Hinj; subst.
      generalize H16 H15 H5 H7 H9 H11; clear; intros.
      evaluate auto_ext.
      descend.
      step auto_ext; eauto.
      rewrite upd_length; omega.
      Transparent evalInstrs.
      simpl in H15.
      match type of H15 with
        | match match ?E with _ => _ end with _ => _ end = _ => destruct E
      end.
      injection H15; intros; subst; auto.
      discriminate.
      simpl in H15.
      match type of H15 with
        | match match ?E with _ => _ end with _ => _ end = _ => destruct E
      end.
      injection H15; intros; subst; auto.
      discriminate.
      Opaque evalInstrs.
    Qed.

    Fixpoint initArgs' (args : list expr) (pos : nat) : list instr :=
      match args with
        | nil => nil
        | arg :: args =>
          IL.Binop Rv (variableSlot "_" ns) Plus (4 * pos)%nat
          :: IL.Assign (LvMem Rv) (exprC arg ns)
          :: initArgs' args (S pos)
      end%SP.

    Lemma initArgs_post1 : forall stn specs args pos pre st,
      interp specs (Structured.Postcondition (toCmd (initArgs args "_" pos) mn H ns res pre) (stn, st))
      -> exists st', interp specs (pre (stn, st'))
        /\ evalInstrs stn st' (initArgs' args pos) = Some st.
    Proof.
      Opaque mult.
      induction args; wrap0; eauto.
      apply IHargs in H2; clear IHargs; do 2 post.
      do 2 eexists; eauto.
      Set Printing Coercions.
      change (Binop (LvReg Rv) (RvLval (variableSlot "_" ns)) Plus
                    (RvImm (natToW (4 * pos)))
                    :: IL.Assign (LvMem (Reg Rv)) (exprC a ns) :: initArgs' args (S pos))
      with ((Binop (LvReg Rv) (RvLval (variableSlot "_" ns)) Plus
                  (RvImm (natToW (4 * pos)))
                  :: IL.Assign (LvMem (Reg Rv)) (exprC a ns) :: nil) ++ initArgs' args (S pos)).
      eauto using evalInstrs_app.
    Qed.      

    Fixpoint multiUpd (ws : list W) (pos : nat) (ws' : list W) : list W :=
      match ws' with
        | nil => ws
        | w :: ws' => multiUpd (Array.updN ws pos w) (S pos) ws'
      end.

    Lemma initArgs_post : forall vs fvs,
      ~In "result" fvs
      -> (forall x e, vs x = Some e
        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
          -> Logic.exprD e fE1 = Logic.exprD e fE2)
      -> forall fE V specs F stn args pos ws args' st st',
        exprsD vs args = Some args'
        -> length ws = pos + length args
        -> ForallF (exprV ns) args
        -> vars_ok fE V vs
        -> interp specs (![ locals ("rp" :: ns) V res (Regs st Sp) * array ws (sel V "_") * F ] (stn, st))
        -> evalInstrs stn st (initArgs' args pos) = Some st'
        -> exists ws', map (fun e => Logic.exprD e fE) args' = map (@Dyn W) ws'
          /\ interp specs (![ locals ("rp" :: ns) V res (Regs st Sp) * array (multiUpd ws pos ws') (sel V "_")
                              * F ] (stn, st'))
          /\ Regs st' Sp = Regs st Sp.
    Proof.
      clear Hmalloc; clear dependent H; induction args; wrap0; simpl in *.

      injection H3; clear H3; intros; subst; simpl.
      exists nil; simpl; intuition.
      Transparent evalInstrs.
      simpl in *.
      congruence.
      simpl in *.
      congruence.
      Opaque evalInstrs.

      do 2 (case_option; try discriminate).
      injection H3; clear H3; intros; subst.
      simpl in *.
      change (Binop (LvReg Rv) (RvLval (variableSlot "_" ns)) Plus
            (RvImm (natToW (4 * pos)))
          :: IL.Assign (LvMem (Reg Rv)) (exprC a ns)
             :: initArgs' args (S pos))
             with ((Binop (LvReg Rv) (RvLval (variableSlot "_" ns)) Plus
            (RvImm (natToW (4 * pos)))
          :: IL.Assign (LvMem (Reg Rv)) (exprC a ns) :: nil)
             ++ initArgs' args (S pos)) in H8.
      apply evalInstrs_app_fwd in H8.
      post.
      eapply exprC_correct in H5; eauto.
      Focus 2.
      instantiate (1 := st).
      instantiate (1 := stn).
      instantiate (1 := (array ws (sel V "_") * F)%Sep).
      instantiate (2 := specs).
      generalize H7; repeat match goal with
                              | [ x : _ |- _ ] => clear x
                            end; intros.
      step auto_ext.
      post.
      rewrite Mult.mult_comm in H8.
      rewrite natToW_times4 in H8.
      rewrite wmult_comm in H8.
      assert (natToW pos < natToW (length ws)).
      apply lt_goodSize; eauto.
      apply goodSize_weaken with (length ws); eauto.
      change (Binop (LvReg Rv) (RvLval (variableSlot "_" ns)) Plus
            (RvImm (natToW 4 ^* natToW pos))
          :: IL.Assign (LvMem (Reg Rv)) (exprC a ns) :: nil)
             with ((Binop (LvReg Rv) (RvLval (variableSlot "_" ns)) Plus
            (RvImm (natToW 4 ^* natToW pos)) :: nil)
          ++ (IL.Assign (LvMem (Reg Rv)) (exprC a ns) :: nil)) in H8.
      apply evalInstrs_app_fwd in H8; post.
      erewrite exprC_uses in H5.
      determine_rvalue.
      generalize dependent H12.
      generalize dependent H10.
      clear H11.
      prep_locals.
      move H15 after H16.
      generalize dependent H6.
      evaluate auto_ext.
      intros.
      eapply IHargs in H12; eauto.
      destruct H12 as [ ? [ ] ].
      exists (x0 :: x2); simpl; intuition.
      generalize H19 H6; repeat match goal with
                                  | [ x : _ |- _ ] => clear x
                                end; intros.
      step auto_ext.
      rewrite updN_length; omega.
      unfold Array.upd in H10.
      rewrite wordToNat_natToWord_idempotent in H10.
      generalize H10 H6; repeat match goal with
                                  | [ x : _ |- _ ] => clear x
                                end; intros.
      step auto_ext.
      change (goodSize pos).
      apply goodSize_weaken with (length (updN ws (wordToNat (natToW pos)) x0)); eauto.
      rewrite updN_length; eauto.

      Transparent evalInstrs.
      simpl in H15.
      match type of H15 with
        | match match ?E with _ => _ end with _ => _ end = _ => destruct E
      end.
      injection H15; intros; subst; auto.
      discriminate.
      simpl in H15.
      match type of H15 with
        | match match ?E with _ => _ end with _ => _ end = _ => destruct E
      end.
      injection H15; intros; subst; auto.
      discriminate.
      Opaque evalInstrs.
    Qed.

    Definition dtFormat (s : string) := (exists s', s = "_D" ++ s')%string.

    Lemma stmtC_vc : forall s (vs : vars) fvs pre post nextDt kC pre0 kD
      (HnextDt : dtFormat nextDt)
      (Hvs : vs "_" = None),
      ~In "result" fvs
      -> normalWf' fvs pre
      -> normalWf' ("result" :: fvs) post
      -> ~In "result" (NQuants pre)
      -> ~In "result" (NQuants post)
      -> scopey fvs post (NImpure post)
      -> scopey' "result" (NImpure pre)
      -> (forall x, In x fvs -> ~In x (NQuants pre))
      -> (forall x, In x fvs -> ~In x (NQuants post))
      -> stmtD dts xs vs fvs pre post nextDt s kD
      -> (forall x e, vs x = Some e
        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
          -> Logic.exprD e fE1 = Logic.exprD e fE2)
      -> (forall specs st,
        interp specs (pre0 st)
        -> interp specs (precond vs pre post true (fun x => x) ns res st))
      -> (forall vs fvs pre post nextDt pre0,
        kD vs fvs pre post nextDt
        -> ~In "result" fvs
        -> normalWf' fvs pre
        -> normalWf' ("result" :: fvs) post
        -> ~In "result" (NQuants pre)
        -> ~In "result" (NQuants post)
        -> scopey fvs post (NImpure post)
        -> scopey' "result" (NImpure pre)
        -> dtFormat nextDt
        -> vs "_" = None
        -> (forall x, In x fvs -> ~In x (NQuants pre))
        -> (forall x, In x fvs -> ~In x (NQuants post))
        -> (forall x e, vs x = Some e
          -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
            -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> (forall specs st,
          interp specs (pre0 st)
          -> interp specs (precond vs pre post true (fun x => x) ns res st))
        -> vcs (VerifCond (toCmd (kC vs fvs pre post nextDt) mn H ns res pre0)))
      -> stmtV dts xs s
      -> vcs (VerifCond (toCmd (stmtC vs fvs pre post nextDt s kC) mn H ns res pre0)).
    Proof.
      induction s.

      (* Assign *)
      wrap0.
      simpl in *; intuition idtac.
      case_option.
      wrap0.
      pre_implies.
      simpl in *; intuition eauto.
      pre_evalu.
      exprC_correct.
      evalu.
      rewriteall.
      case_option.
      apply H14; intuition idtac.
      unfold vars_set.
      destruct (string_dec "_" x); subst; eauto.
      exfalso; eauto.
      unfold vars_set in H18.
      destruct (string_dec x0 x); subst.
      injection H18; clear H18; intros; subst; eauto.
      eauto using exprC_hygienic.
      eauto.
      propxFo.
      pre_implies.
      pre_evalu.
      exprC_correct.
      evalu.
      descend.
      rewrite vars_ok_sel.
      cancl_clear.
      step auto_ext.
      descend; step auto_ext.
      cancl_clear.
      descend; step auto_ext.
      descend; step auto_ext.
      descend; step auto_ext.
      descend; step auto_ext.
      rewriteall.
      use_error_message.

      (* Sequence *)
      wrap0.
      simpl in *; intuition idtac.
      eapply IHs1; intuition eauto.

      (* Return *)
      wrap0.
      pre_implies.
      case_option; simpl in *; intuition eauto.
      pre_evalu.
      exprC_correct.
      evalu.

      pre_implies.
      case_option; simpl in *; intuition eauto.
      pre_evalu.
      exprC_correct.
      evalu.
      case_eq (sentail fvs pre (nsubst "result" e0 post)); intros.
      Focus 2.
      rewrite H26 in *; inversion H11.
      rewrite H26 in *.
      descend.
      step auto_ext.
      step auto_ext.
      descend.
      cancl.
      specialize (sentail_sound fvs (fo_set x0 "result" (Dyn (Regs st Rv))) (@SNil _ _) _ _ _ H26); intuition.
      unfold SubstsH in *; simpl in *.
      eapply Himp_trans; [ | eapply nsubst_bwd; eauto ].
      eapply Himp_trans; [ | apply H23 ].

      eapply weaken_normalD; eauto.
      intros.
      unfold fo_set.
      destruct (string_dec x4 "result"); subst; tauto.
      2: eauto.
      3: simpl; unfold not; intuition (subst; eauto).
      4: simpl; tauto.

      Focus 2.
      unfold fo_set at 1; simpl.
      etransitivity; try (symmetry; apply H20).
      apply H21.
      unfold fo_set; intros.
      destruct (string_dec y "result"); subst; eauto; exfalso; eauto.

      2: simpl; eauto.

      clear H23.
      eapply Forall_forall; intros.
      eapply in_map_iff in H17; destruct H17; intuition subst.
      eapply Forall_forall in H24; try apply H7.
      discriminate.
      eapply Forall_forall in H24; try apply H7.

      eapply wellScoped_psubst.
      eapply wellScoped_weaken; eauto.
      
      simpl; intuition idtac.
      apply in_app_or in H; intuition eauto using in_or_app.
      simpl in *; intuition eauto using in_or_app.
      eauto using in_or_app.

      (* Allocate *)
      Opaque mult.
      wrap0.
      simpl in *; intuition idtac.

      Lemma lookupCon'_locateCon' : forall nm cs,
        List.Forall nconWf cs
        -> forall n,
          match lookupCon' nm cs with
            | Some c => exists tag, locateCon' n nm cs = Some (tag, c)
              /\ nconWf c
            | None => locateCon' n nm cs = None
          end.
      Proof.
        induction 1; simpl; intuition.
        destruct (string_eq nm (NName x)); subst; eauto.
        destruct (lookupCon' nm l); auto.
      Qed.

      Lemma lookupCon_locateCon : forall nm dtName c dts0,
        ndatatypesWf dts0
        -> lookupCon nm dts0 = Some (dtName, c)
        -> exists tag, locateCon nm dts0 = Some (dtName, tag, c)
          /\ nconWf c.
      Proof.
        induction 1; simpl; intuition.
        specialize (lookupCon'_locateCon' nm (snd x) H2 0).
        destruct (lookupCon' nm (snd x)); post.
        injection H4; clear H4; intros; subst.
        rewrite H6; eauto.
        rewrite H5; eauto.
      Qed.

      case_eq (lookupCon conName dts); intros.
      2: rewrite H17 in *; inversion H11.
      rewrite H17 in *.
      destruct p; simpl in *.
      destruct (lookupCon_locateCon _ _ _ _ Hdts H17) as [ ? [ ] ].
      rewrite H19.
      destruct (Peano_dec.eq_nat_dec (length args) (length (NRecursive n) + length (NNonrecursive n))).
      2: inversion H11.
      case_eq (exprsD vs args); intros.
      2: rewrite H21 in *; inversion H11.
      rewrite H21 in *.
      case_eq (cancel fvs ("this" :: nil) pre (allocatePre s n l)); intros.
      2: rewrite H22 in *; inversion H11.
      rewrite H22 in *.
      case_eq (NewSub "this"); intros.
      2: rewrite H23 in *; inversion H11.
      rewrite H23 in *.
      destruct (in_dec string_dec nextDt fvs); try solve [ inversion H11 ].
      Opaque mult.
      wrap0.

      pre_implies.
      clear H22 H15 H18.
      pre_evalu.
      change (locals ("rp" :: ns) x3 res (Regs st Sp))
        with (locals_call ("rp" :: ns) x3 res (Regs st Sp) ("rp" :: "base" :: "n" :: nil) (res - 3) (S (S (S (S 4 * length ns))))) in H15.
      assert (ok_call ("rp" :: ns) ("rp" :: "base" :: "n" :: nil) res (res - 3)
        (S (S (S (S (4 * length ns))))))
      by (split; [ simpl; omega
        | split; [ simpl; omega
          | split; [ NoDup
            | simpl; omega ] ] ] ).
      replace (4 * S (length ns)) with (S (S (S (S (4 * length ns))))) in H15 by omega.
      evalu.

      rewrite Hmalloc; wrap0.
      pre_implies.
      clear H22 H15 H18.
      pre_evalu.
      change (locals ("rp" :: ns) x4 res (Regs x1 Sp))
        with (locals_call ("rp" :: ns) x4 res (Regs x1 Sp) ("rp" :: "base" :: "n" :: nil) 4 (S (S (S (S (4 * length ns)))))) in H15.
      assert (ok_call ("rp" :: ns) ("rp" :: "base" :: "n" :: nil) res 4
        (S (S (S (S (4 * length ns))))))
      by (split; [ simpl; omega
        | split; [ simpl; omega
          | split; [ NoDup
            | simpl; omega ] ] ] ).
      replace (4 * S (length ns)) with (S (S (S (S (4 * length ns))))) in * by omega.
      evalu.
      descend.
      cancl_clear; step auto_ext.
      destruct H20.
      apply le_goodSize; auto; congruence.
      descend; step auto_ext.
      step auto_ext.
      unfold localsInvariant.
      descend; step auto_ext.
      match goal with
        | [ |- interp _ (_ ---> ?Q)%PropX ] => remember Q
      end.
      descend; step auto_ext.

      Lemma sepFormula_Himp : forall P Q,
        P ===> Q
        -> forall specs x, interp specs (![P] x ---> ![Q] x)%PropX.
      Proof.
        rewrite sepFormula_eq.
        intros.
        apply H2.
      Qed.

      eapply Imply_trans.
      eapply sepFormula_Himp.
      apply Himp_star_frame; [ | apply Himp_refl ].
      apply Himp_star_frame; [ apply Himp_refl | ].
      apply Himp_star_frame; [ | apply Himp_refl ].
      apply Himp_star_frame; [ apply Himp_refl | ].

      Lemma allocated_array : forall base len offset,
        allocated base offset len ===> Ex ws, array ws (base ^+ natToW offset) * [| length ws = len |].
      Proof.
        clear; induction len; simpl; intros.

        apply Himp_ex_c; exists nil; sepLemma.

        eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply IHlen ] | ].
        sepLemmaLhsOnly.
        apply Himp_ex_c; exists (x0 :: x); sepLemma.
        unfold array.
        unfold ptsto32m at 2; fold ptsto32m.
        simpl.
        destruct x, offset.
        sepLemma.
        sepLemma.
        etransitivity; [ apply himp_star_comm | ].
        apply himp_star_frame.
        sepLemma.
        etransitivity; [ | apply ptsto32m_shift_base ].
        instantiate (1 := 4).
        replace (base ^+ natToW 4) with (base ^+ natToW 0 ^+ $4) by words.
        change (4 - 4) with 0.
        reflexivity.
        auto.
        etransitivity; [ apply himp_star_comm | ].
        apply himp_star_frame.
        sepLemma.
        etransitivity; [ | apply ptsto32m_shift_base ].
        instantiate (1 := 4).
        change (4 - 4) with 0.
        replace (base ^+ natToW (S offset) ^+ $4) with (base ^+ natToW (S (S (S (S (S offset)))))).
        reflexivity.
        rewrite <- wplus_assoc.
        rewrite <- natToW_plus.
        do 2 f_equal.
        omega.
        auto.
      Qed.

      apply allocated_array.
      eapply Imply_trans; [ apply sepFormula_Himp | ].
      instantiate (1 := (Ex ws, star
        (star (locals ("rp" :: "base" :: "n" :: nil) x8 4 (Regs st Sp))
           (star
              (star
                 ([|Regs x7 Rv = 0 -> False|] *
                  [|freeable (Regs x7 Rv)
                      (wordToNat (natToW (S (Datatypes.length args))))|])
                 (
                  array ws (Regs x7 Rv ^+ natToW 0) *
                  [|Datatypes.length ws = wordToNat (natToW (S (Datatypes.length args)))|]))
              (mallocHeap 0)))
        (SEP.ST.star (normalD pre x2)
           (SEP.ST.star (fun (stn0 : ST.settings) (sm : smem) => x3 (stn0, sm))
              (SEP.ST.star
                 (excessStack (Regs x1 Sp) ("rp" :: ns) res
                    ("rp" :: "base" :: "n" :: nil) 4)
                 (locals ("rp" :: ns) x4 0 (Regs x1 Sp))))))%Sep).
      clear; sepLemma.

      Lemma exout : forall A (P : A -> _) Q st specs,
        (forall x, interp specs (![P x] st ---> Q)%PropX)
        -> interp specs (![ex P] st ---> Q)%PropX.
      Proof.
        rewrite sepFormula_eq; unfold sepFormula_def; intros.
        apply existsL; auto.
      Qed.

      apply exout; intro ws.
      subst p; descend.
      ho.
      rereg.
      rewrite vars_ok_sel.
      cancl_clear.
      rewrite wordToNat_natToWord_idempotent in *
        by (change (goodSize (S (length args))); destruct H20; congruence).
      replace (Regs x7 Rv ^+ natToW 0) with (Regs x7 Rv) by words.
      descend; step auto_ext.
      replace (4 * S (length ns)) with (S (S (S (S (4 * length ns))))) by omega.

      Lemma wplus_wminus : forall u v : W,
        u ^+ v ^- v = u.
      Proof.
        intros; words.
      Qed.

      Lemma wminus_wplus : forall u v : W,
        u ^- v ^+ v = u.
      Proof.
        intros; words.
      Qed.

      rewrite wminus_wplus.
      rewrite H32.
      rewrite H14.
      rewrite wplus_wminus.
      step auto_ext.
      step auto_ext.
      descend; step auto_ext.
      descend; step auto_ext.
      descend; step auto_ext.
      descend; step auto_ext.
      rewrite H33, H32, H14.
      apply wplus_wminus.
      rewrite H32, H14.
      rewrite wplus_wminus.
      apply Imply_refl.

      post.
      rewrite vars_ok_sel in *.
      clear H15 H18 H22 Hmalloc H11.
      evalu.

      post.
      rewrite vars_ok_sel in *.
      clear H15 H18 H22 Hmalloc H11.
      change (IL.Assign (regInL Rv ns) (lvalIn (variableSlot "_") ns)
                        :: IL.Assign (LvMem (Reg Rv)) (immInR (natToW x0) ns) :: nil)
      with ((IL.Assign (regInL Rv ns) (lvalIn (variableSlot "_") ns) :: nil)
                      ++ (IL.Assign (LvMem (Reg Rv)) (immInR (natToW x0) ns) :: nil)) in H25.
      apply evalInstrs_app_fwd_None in H25.
      destruct H25 as [ | [ ? [ ] ] ].
      evalu.
      generalize dependent H15.
      evalu.
      replace (Regs x1 Rv) with (Regs x1 Rv ^+ $4 ^* $0) in H24 by words.
      assert (natToW 0 < natToW (length x3)).
      apply lt_goodSize; auto; eauto 10.
      generalize H25 H15 H24 H32; clear; intros.
      evaluate auto_ext.

      eapply initArgs_vc.
      2: eauto.
      eauto.
      eauto.
      eauto.
      eapply ForallF_weaken; [ | eassumption ].
      intros.
      eapply exprV_weaken; eauto.
      post.
      rewrite vars_ok_sel in *.
      clear H15 H18 H22 H23 H11.
      clear dependent H.
      clear Hres Hmalloc.
      change (IL.Assign (regInL Rv ns) (lvalIn (variableSlot "_") ns)
                        :: IL.Assign (LvMem (Reg Rv)) (immInR (natToW x0) ns) :: nil)
      with ((IL.Assign (regInL Rv ns) (lvalIn (variableSlot "_") ns) :: nil)
                      ++ (IL.Assign (LvMem (Reg Rv)) (immInR (natToW x0) ns) :: nil)) in H26.
      apply evalInstrs_app_fwd in H26.
      destruct H26 as [ ? [ ] ].
      generalize dependent H11.
      evalu.
      replace (Regs x2 Rv) with (Regs x2 Rv ^+ $4 ^* $0) in H24 by words.
      assert (natToW 0 < natToW (length x4)).
      apply lt_goodSize; auto; eauto 10.
      destruct st; unfold fst, snd in *.
      generalize dependent Hvs.
      evaluate auto_ext.

      Lemma vars_ok_unused : forall fE V vs x v,
        vars_ok fE V vs
        -> vs x = None
        -> vars_ok fE (upd V x v) vs.
      Proof.
        unfold vars_ok, upd, sel; intros.
        case_eq (string_eq x0 x); intros.
        apply string_eq_correct in H5; congruence.
        eauto.
      Qed.

      intros; assert (vars_ok x3 (upd x6 "_" (Regs x2 Rv)) vs) by eauto using vars_ok_unused.
      clear Hvs.
      exists x3; exists (upd x6 "_" (Regs x2 Rv)); exists (Array.upd x4 (natToW O) (natToW x0)).
      descend.
      step auto_ext; eauto.

      apply initArgs_post1 in H24; do 2 post.
      clear H23 H15.
      rewrite vars_ok_sel in *.      
      pre_evalu.
      clear H11.
      unfold lvalIn, immInR, regInL in *.
      prep_locals.
      repeat rewrite four_plus_variablePosition in H25 by eauto.

      change (IL.Assign (LvReg Rv)
             (RvLval
                (LvMem (Sp + natToW (variablePosition ("rp" :: ns) "_"))%loc))
           :: IL.Assign (LvMem (Reg Rv)) (RvImm (natToW x0)) :: nil)
             with ((IL.Assign (LvReg Rv)
             (RvLval
                (LvMem (Sp + natToW (variablePosition ("rp" :: ns) "_"))%loc)) :: nil)
           ++ (IL.Assign (LvMem (Reg Rv)) (RvImm (natToW x0)) :: nil)) in H28.
      apply evalInstrs_app_fwd in H28.
      destruct H28; intuition idtac.

      generalize dependent H18.
      generalize dependent Hvs.
      generalize dependent H27.
      generalize dependent H28.
      move H29 after H26.
      clear dependent H.
      evaluate auto_ext.
      replace (Regs x3 Rv) with (Regs x3 Rv ^+ $4 ^* $0) in H15 by words.
      assert (natToW 0 < natToW (length x5)).
      apply lt_goodSize; auto; eauto 10.
      intro; evaluate auto_ext.
      intros Heval ? ?; eapply initArgs_post in Heval.
      Focus 8.
      instantiate (2 := upd x7 "_" (Regs x3 Rv)).
      descend.
      rewrite H18.
      generalize H33; repeat match goal with
                               | [ x : _ |- _ ] => clear x
                             end; intros.
      instantiate (3 := specs).
      step auto_ext.
      3: eauto.
      2: eauto.
      2: eauto.
      2: rewrite upd_length; eauto.
      2: eapply ForallF_weaken; [ | eassumption ]; intros; eapply exprV_weaken; eauto.
      2: eauto using vars_ok_unused.
      destruct Heval as [ ? [ ? [ ] ] ].
      clear H34 H35 H33 Hvs.
      assert (In x ("rp" :: ns)) by (simpl; intuition eauto). 
      evaluate auto_ext.

      (* Final VC here. *)

      Lemma dtFormat_prime : forall s, dtFormat s
        -> dtFormat (s ++ "'")%string.
      Proof.
        unfold dtFormat; post.
        exists (x ++ "'")%string.
        subst; auto.
      Qed.

      Hint Immediate dtFormat_prime.

      Lemma set_dummy : forall vs x e,
        vs "_" = None
        -> In x xs
        -> vars_set vs x e "_" = None.
      Proof.
        unfold vars_set; intros.
        destruct (string_dec "_" x); congruence.
      Qed.

      Hint Immediate set_dummy.

      apply H14; clear H14; simpl; intuition eauto.
      subst; destruct HnextDt; discriminate.

      Lemma normalWf_weaken : forall fvs1 fvs2 n,
        normalWf fvs1 n
        -> (forall x, In x fvs1 -> In x fvs2)
        -> (forall x, In x fvs2 -> In x fvs1 \/ ~good_fo_var x)
        -> normalWf fvs2 n.
      Proof.
        destruct 1; split; eauto.

        eapply Forall_weaken; try apply WellScoped; intros.
        eapply wellScoped_weaken; eauto.
        intros.
        apply in_app_or in H5; intuition.

        eapply Forall_weaken; try apply NoClash; intros.
        post.
        descend; eauto.
        intuition idtac.
        apply H6; auto.
        specialize (fun x H => proj2 (H6 x H)).
        apply in_app_or in H7; intuition eauto using in_or_app.
        apply H3 in H9; intuition eauto using in_or_app.
        apply H7.
        apply H6; auto.

        destruct (NPure n); intuition.
        apply GoodPure; intuition.
        intros.
        apply H3 in H4; intuition eauto.
        eapply Forall_forall in GoodQuantNames; eauto.
      Qed.

      Lemma dtFormat_not_good : forall x, dtFormat x
        -> good_fo_var x
        -> False.
      Proof.
        destruct 1; subst; tauto.
      Qed.

      Hint Immediate dtFormat_not_good.

      Focus 2.
      eapply normalWf_weaken; eauto.
      simpl; intuition eauto.
      simpl; intuition (subst; eauto).
      Focus 4.
      subst.
      eapply Forall_forall in H24; [ | eapply GoodQuantNames; eauto ].
      eauto.
      Focus 4.
      subst.
      eapply Forall_forall in H24; [ | eapply GoodQuantNames; eauto ].
      eauto.

      Lemma scopey_weaken : forall fvs1 fvs2 post ns,
        scopey fvs1 post ns
        -> (forall x, In x fvs1 -> In x fvs2)
        -> scopey fvs2 post ns.
      Proof.
        intros; eapply Forall_weaken; [ | eauto ].
        intros.
        eapply wellScoped_weaken; eauto.
        intros.
        apply in_app_or in H5; intuition eauto using in_or_app.
        simpl in H6; intuition (subst; eauto using in_or_app).
        apply in_or_app; simpl; tauto.
        apply in_or_app; simpl; eauto.
      Qed.

      Focus 2.
      eapply scopey_weaken; eauto.
      simpl; tauto.

      Focus 3.
      unfold vars_set in H14.
      destruct (string_dec x1 x); subst; eauto.
      injection H14; clear H14; intros; subst; simpl.
      eauto.

      Lemma normalWf_new_impure : forall fvs n p,
        normalWf fvs n
        -> List.Forall (wellScoped (NQuants n ++ fvs)) p
        -> List.Forall (fun p => exists bvs, boundVars p = Some bvs
                         /\ forall x, In x bvs -> good_fo_var x /\ ~In x (NQuants n ++ fvs)) p
        -> normalWf fvs {| NQuants := NQuants n;
                           NPure := NPure n;
                           NImpure := p |}.
      Proof.
        destruct 1; split; simpl; intuition.
      Qed.

      eapply normalWf_new_impure; eauto.
      eapply normalWf_weaken; eauto.
      simpl; intuition eauto.
      simpl; intuition (subst; eauto).
      constructor.
      simpl; intuition subst; simpl.

      Lemma findMatching_NewLhs : forall fvs' rhs lhs s NewSub NewLhs ProveThese,
        findMatching fvs' s lhs rhs = Success1 NewSub NewLhs ProveThese
        -> forall x, In x NewLhs -> In x lhs.
      Proof.
        clear; induction lhs; simpl; intuition.
        
        case_eq (unify_pred fvs' s a rhs); intros.
        rewrite H1 in *.
        destruct p.
        injection H; clear H; intros; subst; tauto.
        rewrite H1 in *.
        case_eq (findMatching fvs' s lhs rhs); intros.
        rewrite H2 in *.
        injection H; clear H; intros; subst; eauto.
        simpl in H0; intuition eauto.
        rewrite H2 in *; discriminate.
      Qed.

      Lemma findMatchings_NewLhs : forall fvs' rhs lhs s NewSub NewLhs ProveThese,
        findMatchings fvs' s lhs rhs = Success1 NewSub NewLhs ProveThese
        -> forall x, In x NewLhs -> In x lhs.
      Proof.
        clear; induction rhs; simpl; intuition.

        case_eq (findMatching fvs' s lhs a); intros.
        2: rewrite H1 in *; discriminate.
        rewrite H1 in *.
        case_eq (findMatchings fvs' NewSub0 NewLhs0 rhs); intros.
        2: rewrite H2 in *; discriminate.
        rewrite H2 in *.
        injection H; clear H; intros; subst.
        eauto using findMatching_NewLhs.
      Qed.

      Lemma unify_expr_NewSub_wellFormed : forall fvs' fvs e1 e2 s s' fs,
        unify_expr fvs' s e1 e2 = Some (s', fs)
        -> (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                            -> Logic.exprD e1 fE1 = Logic.exprD e1 fE2)
        -> (forall x e, s x = Some e
                        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                                           -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> forall x e, s' x = Some e
          -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                             -> Logic.exprD e fE1 = Logic.exprD e fE2.
      Proof.
        clear; destruct e1, e2; simpl; intuition.
        destruct (in_dec string_dec x0 fvs'); try discriminate.
        case_eq (s x0); intros.
        rewrite H4 in *.
        destruct e0; try discriminate.
        destruct (string_dec x2 x); subst; try discriminate.
        injection H; clear H; intros; subst.
        eauto.
        rewrite H4 in *.
        injection H; clear H; intros; subst.
        unfold fos_set in H2.
        destruct (string_dec x1 x0); subst; eauto.
        injection H2; clear H2; intros; subst; simpl.
        eauto.

        destruct (in_dec string_dec x fvs'); try discriminate.
        case_eq (s x); intros.
        rewrite H4 in *.
        destruct e0; try discriminate.
        injection H; clear H; intros; subst.
        eauto.
        rewrite H4 in *.
        injection H; clear H; intros; subst.
        unfold fos_set in H2.
        destruct (string_dec x0 x); subst; eauto.
        injection H2; clear H2; intros; subst; simpl.
        eauto.

        injection H; clear H; intros; subst; eauto.
      Qed.

      Lemma unify_args_NewSub_wellFormed : forall fvs fvs' es1 es2 s s' fs,
        unify_args fvs' s es1 es2 = Some (s', fs)
        -> (forall e, In e es1
                      -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                                         -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> (forall x e, s x = Some e
                        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                                           -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> forall x e, s' x = Some e
          -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                             -> Logic.exprD e fE1 = Logic.exprD e fE2.
      Proof.
        clear; induction es1; destruct es2; simpl; intuition.
        injection H; clear H; intros; subst; eauto.
        case_eq (unify_expr fvs' s a e); intros.
        rewrite H4 in *.
        destruct p.
        case_eq (unify_args fvs' f es1 es2); intros.
        rewrite H5 in *.
        destruct p.
        injection H; clear H; intros; subst.
        eauto 7 using unify_expr_NewSub_wellFormed.
        rewrite H5 in *; discriminate.        
        rewrite H4 in *; discriminate.
      Qed.

      Lemma unify_pred_NewSub_wellFormed : forall fvs fvs' p1 p2 s s' fs,
        unify_pred fvs' s p1 p2 = Some (s', fs)
        -> wellScoped fvs p1
        -> (forall x e, s x = Some e
                        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                                           -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> forall x e, s' x = Some e
          -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                             -> Logic.exprD e fE1 = Logic.exprD e fE2.
      Proof.
        clear; induction p1; destruct p2; simpl; intuition.
        destruct (string_dec X X0); subst; try discriminate.
        eauto using unify_args_NewSub_wellFormed.
      Qed.

      Lemma findMatching_NewSub_wellFormed : forall fvs fvs' rhs lhs s NewSub NewLhs ProveThese,
        findMatching fvs' s lhs rhs = Success1 NewSub NewLhs ProveThese
        -> List.Forall (wellScoped fvs) lhs
        -> (forall x e, s x = Some e
                        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                                           -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> forall x e, NewSub x = Some e
          -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                             -> Logic.exprD e fE1 = Logic.exprD e fE2.
      Proof.
        clear; induction lhs; simpl; intuition.
        
        inversion_clear H0.
        case_eq (unify_pred fvs' s a rhs); intros.
        rewrite H0 in *.
        destruct p.
        injection H; clear H; intros; subst.
        eauto using unify_pred_NewSub_wellFormed.
        rewrite H0 in *.
        case_eq (findMatching fvs' s lhs rhs); intros.
        rewrite H6 in *.
        injection H; clear H; intros; subst; eauto.
        rewrite H6 in *; discriminate.
      Qed.

      Lemma findMatchings_NewSub_wellFormed : forall fvs fvs' rhs lhs s NewSub NewLhs ProveThese,
        findMatchings fvs' s lhs rhs = Success1 NewSub NewLhs ProveThese
        -> List.Forall (wellScoped fvs) lhs
        -> (forall x e, s x = Some e
                        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                                           -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> forall x e, NewSub x = Some e
          -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
                             -> Logic.exprD e fE1 = Logic.exprD e fE2.
      Proof.
        clear; induction rhs; simpl; intuition.

        injection H; clear H; intros; subst; eauto.

        case_eq (findMatching fvs' s lhs a); intros.
        2: rewrite H4 in *; discriminate.
        rewrite H4 in *.
        case_eq (findMatchings fvs' NewSub0 NewLhs0 rhs); intros.
        2: rewrite H5 in *; discriminate.
        rewrite H5 in *.
        injection H; clear H; intros; subst.
        eapply IHrhs; eauto.
        eapply Forall_forall; intros.
        eapply findMatching_NewLhs in H; [ | eauto ].
        eapply Forall_forall in H0; eauto.
        eauto using findMatching_NewSub_wellFormed.
      Qed.

      Lemma cancel_NewSub_wellFormed : forall fvs evs lhs rhs NewSub NewLhs ProveThis,
        cancel fvs evs lhs rhs = Success NewSub NewLhs ProveThis
        -> normalWf fvs lhs
        -> forall x e, NewSub x = Some e
          -> forall fE1 fE2, (forall y, In y (NQuants lhs ++ fvs) -> fE1 y = fE2 y)
                             -> Logic.exprD e fE1 = Logic.exprD e fE2.
      Proof.
        unfold cancel; intros.
        case_eq (findMatchings (evs ++ NQuants rhs)
                               (fun x => if in_dec string_dec x fvs then Some (Logic.Var x) else None)
                               (NImpure lhs) (NImpure rhs)); intros.
        2: rewrite H6 in *; discriminate.
        rewrite H6 in *.
        injection H2; clear H2; intros; subst.
        eapply findMatchings_NewSub_wellFormed.
        eauto.
        destruct H3; eauto.
        2: eauto.
        simpl; intros.
        destruct (in_dec string_dec x0 fvs); try discriminate.
        injection H2; clear H2; intros; subst; simpl.
        eauto using in_or_app.
        eauto.
      Qed.

      eapply cancel_NewSub_wellFormed in H22; eauto.
      intros.
      apply in_app_or in H24; intuition.
      apply H14.
      apply in_or_app; simpl; tauto.

      Lemma cancel_NewLhs : forall fvs evs lhs rhs NewSub NewLhs ProveThis,
        cancel fvs evs lhs rhs = Success NewSub NewLhs ProveThis
        -> forall x, In x NewLhs -> In x (NImpure lhs).
      Proof.
        unfold cancel; intros.
        case_eq (findMatchings (evs ++ NQuants rhs)
                               (fun x => if in_dec string_dec x fvs then Some (Logic.Var x) else None)
                               (NImpure lhs) (NImpure rhs)); intros.
        2: rewrite H4 in *; discriminate.
        rewrite H4 in *.
        injection H2; clear H2; intros; subst.
        eauto using findMatchings_NewLhs.
      Qed.

      apply Forall_forall; intros.
      eapply cancel_NewLhs in H22.
      destruct H3.
      eapply Forall_forall in WellScoped; [ | eauto ].
      2: eauto.
      eapply wellScoped_weaken; eauto.
      intros.
      apply in_app_or in H3; intuition.
      constructor.
      simpl; intuition subst; simpl.
      exists nil; simpl; tauto.
      apply Forall_forall; intros.
      eapply cancel_NewLhs in H22.
      destruct H3.
      eapply Forall_forall in NoClash; [ | eauto ].
      2: eauto.
      destruct NoClash as [ ? [ ] ].
      descend; eauto.
      split.
      apply H24; auto.
      intro.
      apply in_app_or in H26; simpl in H26; intuition (subst; eauto).
      eapply H24; eauto using in_or_app.
      2: eapply H24; eauto using in_or_app.
      apply H24 in H25.
      destruct H25.
      eauto.
      hnf.
      constructor.
      simpl; eauto.
      apply Forall_forall; intro.
      intros.
      eapply Forall_forall in H8; eauto.
      eapply cancel_NewLhs in H22; eauto.

      (* Finally, prove that we computed a good postcondition. *)
      admit.
    Qed.
  End chunk_params.
End stmtC.


Local Hint Immediate wellScoped_predExt.

Lemma scopey_normalize : forall fvs post post' bvs',
  wellScoped ("result" :: fvs) post
  -> boundVars post = Some bvs'
  -> (forall x, In x bvs' -> ~In x ("result" :: fvs))
  -> (forall x, In x bvs' -> good_fo_var x)
  -> post' = normalize post
  -> scopey fvs post' (NImpure post').
Proof.
  intros; subst.
  eapply normalize_wf in H0; eauto; intuition.
Qed.

Local Hint Immediate scopey_normalize.
Local Hint Resolve normalize_boundVars.

Lemma normalize_NImpure_keeps : forall p fvs bvs,
  wellScoped fvs p
  -> boundVars p = Some bvs
  -> (forall x, In x bvs -> ~In x fvs)
  -> ~In "result" bvs
  -> scopey' "result" (NImpure (normalize p)).
Proof.
  unfold scopey'; induction p; simpl; intuition eauto.

  caser.
  apply Forall_app; eauto 10 using in_or_app.

  caser.
  eapply IHp.
  eauto.
  eauto.
  2: eauto.
  simpl; intuition (subst; eauto using In_notInList).
Qed.

Local Hint Immediate normalize_NImpure_keeps.

Lemma dtFormat_D : dtFormat "_D".
Proof.
  exists ""; auto.
Qed.

Local Hint Resolve dtFormat_D.

(** Main statement compiler/combinator/macro *)
Definition Stmt
  (dts : list datatype)
  (* Available algebraic datatypes *)
  (fvs : list fo_var)
  (* Logical variables available to mention *)
  (bvs bvs' : list fo_var)
  (* Logical variables bound within [pre] and [post] *)
  (xs : list pr_var)
  (* Program variables available to mention *)
  (vs : vars)
  (* Symbolic valuation to those variables *)
  (pre post : pred)
  (* The Depl-level separation-logic specification for this statement *)
  (s : stmt)
  (* The statement to compile *)
  : chunk.
Proof.
  pose (dts' := map normalizeDatatype dts).
  pose (pre' := normalize pre).
  pose (post' := normalize post).
  apply (WrapC (stmtC dts' vs fvs pre' post' "_D" s (fun _ _ _ _ _ => Fail))
    (precond vs pre' post')
    (fun _ _ _ _ _ => [| False |])%PropX
    (* Unsatisfiable postcondition, since we won't allow running off the end of
     * a function body without returning *)

    (* VERIFICATION CONDITION *)
    (fun im ns res =>
      incl xs ns
      :: (~In "rp" ns)
      :: stmtV dts' xs s
      :: (forall x e, vs x = Some e
        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
          -> Logic.exprD e fE1 = Logic.exprD e fE2)
      :: wellScoped fvs pre
      :: wellScoped ("result" :: fvs) post
      :: (boundVars pre = Some bvs)
      :: (boundVars post = Some bvs')
      :: (forall x, In x bvs -> ~In x fvs)
      :: (forall x, In x bvs -> good_fo_var x)
      :: (forall x, In x bvs' -> ~In x ("result" :: fvs))
      :: (forall x, In x bvs' -> good_fo_var x)
      :: (~In "result" fvs)
      :: (~In "result" bvs)
      :: (~In "result" bvs')
      :: stmtD dts' xs vs fvs pre' post' "_D" s (fun _ _ _ _ _ => False)
      :: ndatatypesWf dts'
      :: (res >= 7)%nat
      :: "malloc"!"malloc" ~~ im ~~> Malloc.mallocS
      :: In "_" ns
      :: (~In "_" xs)
      :: (vs "_" = None)
      :: nil)); [
        abstract (wrap0; match goal with
                           | [ H : interp _ _ |- _ ] => eapply stmtC_post in H; eauto; repeat (post; eauto 6)
                         end; post)
        | abstract (wrap0; match goal with
                             | [ H : wellScoped _ _ |- _ ] =>
                               solve [ eapply stmtC_vc; [  | | | | | | | | | |
                                                           eapply normalize_wf; try apply H; eauto 2
                                                           | eapply normalize_wf; eauto
                                                           | .. ];
                               unfold pre', post'; eauto 6; cbv beta; tauto ]
                           end) ].
Defined.
