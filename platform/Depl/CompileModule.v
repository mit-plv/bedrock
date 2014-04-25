(** Compiling the deeply embedded programming language *)

Require Import Bool.

Require Import AutoSep Wrap Malloc.

Require Import Depl.Logic Depl.AlgebraicDatatypes Depl.Statements Depl.Compile.


(** * Functions *)

(** Type of one function in a Depl module *)
Record function := {
  Name : string;
  (** This name is copied over verbatim into the Bedrock module. *)

  SpecVars : list fo_var;
  (** Spec variables scoped over both precondition and postcondition *)

  Formals : list pr_var;
  (** Formal function argument names *)

  Locals : list pr_var;
  (** Other available variables *)

  Precondition : pred;
  Postcondition : pred;
  Body : stmt
  (** Yeah, you know what these are. *)
}.

(** Helper to copy formal parameter values from a [vals] to a [fo_env] *)
Fixpoint formals (V : vals) (xs : list pr_var) (fE : fo_env) : fo_env :=
  match xs with
    | nil => fE
    | x :: xs => fo_set (formals V xs fE) (x ++ "0")%string (Dyn (sel V x))
  end.

Section dts.
  Variable dts : list datatype.

  (** Generic top-level function spec (see [Compile.precond] for comments) *)
  Definition precond (frmls lcls : list pr_var) (pre post : pred) (inBody : bool) : assert :=
    (Al fE,
      PRE[V] mallocHeap 0 * predD dts pre (formals V frmls fE)
      POST[R] mallocHeap 0 * predD dts post (fo_set (formals V frmls fE) "result" (Dyn R)))
    inBody (fun w => w) (if inBody then frmls ++ lcls else frmls) (if inBody then 7 else 7 + length lcls).

  (** A default function, for when things go horribly wrong *)
  Definition function0 name : Programming.function := {|
    FName := name;
    FVars := nil;
    FReserved := 0;
    FPrecondition := (st ~> [| False |]);
    FBody := Skip
  |}.

  (** Initial symbolic variable assignment *)
  Definition vars0 (xs : list pr_var) : vars := 
    fun x => if in_dec string_dec x xs then Some (Logic.Var (x ++ "0")%string) else None.

  (** Generating one Bedrock function *)
  Definition compileFunction (f : function) : Programming.function :=
    let xs := Formals f ++ Locals f in
    match boundVars (Precondition f), boundVars (Postcondition f) with
      | Some bvs, Some bvs' => {|
        FName := Name f;
        FVars := Formals f;
        FReserved := 7 + length (Locals f);
        FPrecondition := precond (Formals f) ("_" :: Locals f)
                                 (Precondition f) (Postcondition f) false;
        FBody := ($[Sp+0] <- Rp;;
          (fun _ _ =>
            Structured nil (fun im mn _ => Structured.Assert_ im mn
              (precond (Formals f) ("_" :: Locals f) (Precondition f) (Postcondition f) true)));;
          (fun _ _ => Stmt dts (map (fun s => s ++ "0")%string xs ++ SpecVars f)
            bvs bvs' xs (vars0 (Formals f))
            (Precondition f) (Postcondition f) (Body f)
            (Formals f ++ "_" :: Locals f) 7))%SP
      |}
      | _, _ => function0 (Name f)
    end.

  (** Deciding whether a list is duplicate-free *)
  Section NoDup_dec.
    Variable A : Type.
    Variable dec : forall x y : A, {x = y} + {x <> y}.

    Hint Constructors NoDup.

    Definition NoDup_dec : forall ls : list A, {NoDup ls} + {~NoDup ls}.
    Proof.
      refine (fix NoDup_dec (ls : list A) : {NoDup ls} + {~NoDup ls} :=
        match ls return {NoDup ls} + {~NoDup ls} with
          | nil => left _
          | x :: ls' => if in_dec dec x ls' then right _ else
            if NoDup_dec ls' then left _ else right _
        end); clear NoDup_dec; abstract (eauto; inversion_clear 1; tauto).
    Defined.
  End NoDup_dec.

  (** Does a list of variables include any ending in "0"?
    * We're using that convention for our automatically generated variables,
    * so it's a no-no for the programmer to use it. *)

  Fixpoint anyZero (x : fo_var) : bool :=
    match x with
      | "" => false
      | "0" => true
      | String _ x' => anyZero x'
    end.

  Fixpoint anyZeros (xs : list fo_var) : bool :=
    match xs with
      | nil => false
      | x :: xs' => anyZero x || anyZeros xs'
    end.

  Fixpoint good_vars (xs : list fo_var) : bool :=
    match xs with
      | nil => true
      | x :: xs => match x with
                     | String "_" _ => false
                     | _ => good_vars xs
                   end
    end.

  (** A computable syntactic well-formedness check... *)
  Definition functionWf (f : function) : bool :=
    let xs' := Formals f ++ Locals f in
    let xs := Formals f ++ "_" :: Locals f in
    let fvs := map (fun s => s ++ "0")%string xs' ++ SpecVars f in
    notInList "rp" xs' && notInList "result" fvs
    && (if NoDup_dec _ string_dec xs' then true else false)
    && negb (anyZeros (SpecVars f)) && notInList "result" (SpecVars f)
    && match boundVars (Precondition f), boundVars (Postcondition f) with
         | Some bvs, Some bvs' =>
           notInList "result" bvs && notInList "result" bvs'
           && notInList "this" bvs && notInList "this" bvs'
           && notsInList bvs fvs && notsInList bvs' ("result" :: fvs)
           && good_vars bvs && good_vars bvs'
           && good_vars (Formals f) && good_vars (Locals f)
           && notInList "this" (SpecVars f)
         | _, _ => false
       end.

  Section dts'.
    Variable dts' : list ndatatype.

    (** ...and a residual part, for what we ask the user to prove *)
    Definition functionVc (f : function) : list Prop :=
      let xs := Formals f ++ Locals f in
      let fvs := map (fun s => s ++ "0")%string xs ++ SpecVars f in
        stmtV dts' xs (Body f)
        :: wellScoped fvs (Precondition f)
        :: wellScoped ("result" :: fvs) (Postcondition f)
        :: stmtD dts' xs (vars0 (Formals f)) fvs (normalize (Precondition f))
        (normalize (Postcondition f)) "_D" (Body f) (fun _ _ _ _ _ => False)
        :: nil.

    (** Combined syntactic check for all functions *)
    Fixpoint functionsWf (fs : list function) : bool :=
      match fs with
        | nil => true
        | f :: fs' => functionWf f && functionsWf fs'
      end.

    (** Combine the VCs of all functions. *)
    Fixpoint makeVcs (fs : list function) : list Prop :=
      match fs with
        | nil => nil
        | f :: fs' => functionVc f ++ makeVcs fs'
      end.

    Ltac clear_fancier := clear_fancy;
      repeat match goal with
               | [ H : context[map] |- _ ] => clear H
             end.

    Lemma sel_eta : forall V, sel V = V.
    Proof.
      auto.
    Qed.

    Theorem normalize_sound_fwd : forall p fvs bvs fE,
      wellScoped fvs p
      -> boundVars p = Some bvs
      -> (forall x, In x fvs -> ~In x bvs)
      -> predD dts p fE ===> normalD dts (normalize p) fE.
    Proof.
      intros.
      change (predD dts p fE) with (SubstsH (SNil _ _) (predD dts p fE)).
      change (normalD dts (normalize p) fE) with (SubstsH (SNil _ _) (normalD dts (normalize p) fE)).
      eapply normalize_sound_fwd; eauto.
    Qed.

    Theorem normalize_sound_bwd : forall p fvs bvs fE,
      wellScoped fvs p
      -> boundVars p = Some bvs
      -> (forall x, In x fvs -> ~In x bvs)
      -> normalD dts (normalize p) fE ===> predD dts p fE.
    Proof.
      intros.
      change (predD dts p fE) with (SubstsH (SNil _ _) (predD dts p fE)).
      change (normalD dts (normalize p) fE) with (SubstsH (SNil _ _) (normalD dts (normalize p) fE)).
      eapply normalize_sound_bwd; eauto.
    Qed.

    Lemma weaken_predD : forall p xs fE fE',
      wellScoped xs p
      -> (forall x, In x xs -> fE x = fE' x)
      -> predD dts p fE ===> predD dts p fE'.
    Proof.
      intros.
      change (predD dts p fE) with (SubstsH (SNil _ _) (predD dts p fE)).
      change (predD dts p fE') with (SubstsH (SNil _ _) (predD dts p fE')).
      eapply weaken_predD; eauto.
    Qed.

    Hypothesis Hnodup : nodup dts.
    Hypothesis Hndts : ndts_good dts dts'.
    Hypothesis Hdts : datatypesWf dts.

    (** Relate the above definitions to what [StructuredModule] wants. *)
    Theorem makeVcs_correct : forall mn fs0 fs (Hmn : mn <> "malloc"), functionsWf fs = true
      -> vcs (makeVcs fs)
      -> vcs (StructuredModule.makeVcs
                (("malloc", "malloc", Programming.Precondition mallocS None) :: nil) fs0
        (map (fun p => match p with
                         | {| FName := f; FVars := ns; FReserved := res;
                           FPrecondition := pre; FBody := ch |} =>
                         (f, pre, fun im' H => toCmd ch mn H ns res)
                       end)
        (map compileFunction fs))).
    Proof.
      induction fs; simpl; intuition.
      apply andb_prop in H; intuition.
      unfold functionWf in H2.
      unfold compileFunction at 1.

      repeat match goal with
               | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; destruct H
               | [ H : negb _ = true |- _ ] => apply negb_true_iff in H
               | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; try discriminate
               | [ H : context[match ?E with None => _ | _ => _ end] |- _ ] => case_eq E; intros;
                 match goal with
                   | [ H' : _ = _ |- _ ] => rewrite H' in *
                 end; try discriminate
             end.
      simpl.
      wrap0.

      post; clear_fancier.
      assert (In "rp" ("rp" :: Formals a)) by (simpl; tauto).
      assert (~In "rp" (Formals a))
        by (intro; eapply In_notInList; try apply H1; eauto using in_or_app).
      change (sel x1) with x1 in *.
      unfold lvalIn, regInL in *; simpl in H1.
      change (LvMem (Indir Sp (natToW O))) with (LvMem (Indir Sp (variablePosition ("rp" :: Formals a) "rp"))) in *.
      evaluate auto_ext.

      post.
      assert (forall x4 x v, In x (map (fun s : string => (s ++ "0")%string) (Formals a ++ Locals a) ++ SpecVars a)
        -> formals x2 (Formals a) x0 x
        = formals (upd (merge x2 x4 ("rp" :: Formals a)) "rp" v)
        (Formals a) x0 x).
      intros.
      apply in_app_or in H; intuition idtac.
      apply in_map_iff in H29; destruct H29; intuition subst.

      Lemma append0_invert : forall x y,
        (x ++ "0" = y ++ "0")%string
        -> x = y.
      Proof.
        induction x; destruct y; simpl in *; intuition.
        destruct y; discriminate.
        destruct x; discriminate.
        injection H; clear H; intros; subst.
        f_equal; auto.
      Qed.

      Lemma formals_switch : forall V V' x xs fE,
        (In x xs -> sel V x = sel V' x)
        -> formals V xs fE (x ++ "0")%string = formals V' xs fE (x ++ "0")%string.
      Proof.
        induction xs; simpl; intuition.
        unfold fo_set.
        destruct (string_dec (x ++ "0")%string (a ++ "0")%string); subst; auto.
        apply append0_invert in e; subst.
        f_equal; auto.
      Qed.

      apply formals_switch.
      apply in_app_or in H30; intuition idtac.
      rewrite sel_upd_ne.
      symmetry; apply sel_merge.
      simpl; tauto.
      intro; subst.
      eauto using in_or_app, In_notInList.
      simpl in H29; intuition subst.
      rewrite sel_upd_ne.
      symmetry; apply sel_merge.
      simpl; tauto.

      Lemma NoDup_unapp : forall A (ls2 ls1 : list A),
        NoDup (ls1 ++ ls2)
        -> forall x, In x ls1 -> In x ls2 -> False.
      Proof.
        induction ls1; inversion 1; simpl; intuition (subst; eauto using in_or_app).
      Qed.

      exfalso; eauto using NoDup_unapp, NoDup_remove_1.

      Lemma anyZero_duh : forall s, anyZero (s ++ "0")%string = true.
      Proof.
        induction s; simpl; intuition.
        destruct a.
        rewrite IHs.
        repeat match goal with
                 | [ |- (if ?E then _ else _) = _ ] => destruct E; auto
               end.
      Qed.

      Lemma formals_irrel : forall V V' x xs fE,
        anyZero x = false
        -> formals V xs fE x = formals V' xs fE x.
      Proof.
        induction xs; simpl; intuition.
        unfold fo_set.
        destruct (string_dec x (a ++ "0")%string); subst; auto.
        rewrite anyZero_duh in H; discriminate.
      Qed.

      Lemma anyZeros_correct : forall x xs, anyZeros xs = false
        -> In x xs
        -> anyZero x = false.
      Proof.
        induction xs; simpl; intuition subst.

        apply orb_false_iff in H; intuition.
        apply orb_false_iff in H; intuition.
      Qed.

      eauto using formals_irrel, anyZeros_correct.

      generalize dependent (map (fun s : string => (s ++ "0")%string) (Formals a ++ Locals a) ++ SpecVars a); intros.
      clear_fancier.
      change (locals ("rp" :: Formals a) x2 (S (S (S (S (S (S (S (S (length (Locals a))))))))))
          (Regs x Sp))
        with (locals_in ("rp" :: Formals a) x2 (S (S (S (S (S (S (S (S (length (Locals a))))))))))
          (Regs x Sp)
          ("_" :: Locals a) ("rp" :: Formals a ++ "_" :: Locals a) 7) in *.
      assert (ok_in ("rp" :: Formals a) (S (S (S (S (S (S (S (S (length (Locals a))))))))))
        ("_" :: Locals a) ("rp" :: Formals a ++ "_" :: Locals a) 7).
      repeat split; unfold pr_var; auto; try omega.
      simpl; omega.
      simpl; constructor; auto.
      intro.
      apply in_app_or in H0; intuition subst.
      eauto using In_notInList, in_or_app.
      simpl in H26; intuition subst.
      discriminate.
      eapply In_notInList; try apply H1.
      apply in_or_app; simpl; tauto.
      apply NoDup_app.
      eauto using NoDup_unapp1.
      constructor; eauto using NoDup_unapp2.
      intros.

      Theorem good_vars_sound : forall xs, good_vars xs = true
        -> List.Forall good_fo_var xs.    
      Proof.
        induction xs; simpl; intuition.
        destruct a.
        constructor; auto; constructor.
        repeat match goal with
                 | [ _ : match ?E with _ => _ end = _ |- _ ] => destruct E; auto
               end; constructor; auto; discriminate || constructor.
      Qed.

      intro.
      apply good_vars_sound in H11.
      eapply Forall_forall in H11; try eassumption.
      destruct H11.
      intros.
      intro.
      simpl in H26; intuition subst.
      apply good_vars_sound in H12.
      eapply Forall_forall in H12; try eassumption.
      destruct H12.
      eauto using NoDup_unapp.
      simpl length; omega.
      assert (In "rp" ("rp" :: Formals a ++ "_" :: Locals a)) by (simpl; tauto).
      change (sel x2) with x2 in *.
      unfold lvalIn, regInL in *; simpl in H25.
      change (LvMem (Indir Sp (natToW O))) with (LvMem (Indir Sp (variablePosition ("rp" :: Formals a ++ "_" :: Locals a) "rp"))) in *.
      clear H24.
      evaluate auto_ext.
      fold (@app pr_var) in *.
      descend.
      rewrite sel_eta.
      step auto_ext.
      etransitivity; [ apply himp_star_comm | ]; apply himp_star_frame; try reflexivity.
      eapply weaken_predD; eauto.
      eauto.
      step auto_ext.
      descend; step auto_ext.
      instantiate (1 := x6).
      change (locals ("rp" :: Formals a) x6
          (S (S (S (S (S (S (S (S (Datatypes.length (Locals a)))))))))) (Regs x Sp))
        with (locals_out ("rp" :: Formals a) x6
          (S (S (S (S (S (S (S (S (Datatypes.length (Locals a))))))))))
          (Regs x Sp) ("_" :: Locals a) ("rp" :: Formals a ++ "_" :: Locals a) 7).
      assert (ok_out ("rp" :: Formals a)
        (S (S (S (S (S (S (S (S (Datatypes.length (Locals a))))))))))
        ("_" :: Locals a) ("rp" :: Formals a ++ "_" :: Locals a) 7).
      repeat split; unfold pr_var; auto; try omega.
      simpl; omega.
      simpl length; omega.
      rewrite sel_eta.
      descend; step auto_ext.
      eapply weaken_predD; eauto.
      simpl; intuition (subst; eauto).
      unfold fo_set.
      destruct (string_dec x6 "result"); subst; auto.
      symmetry; auto.


      post.
      generalize dependent (map (fun s : string => (s ++ "0")%string) (Formals a ++ Locals a) ++ SpecVars a); intros.
      clear_fancier.
      clear H24.
      descend.
      repeat rewrite sel_eta in *.
      step auto_ext.
      Focus 2.
      apply himp_star_frame; try reflexivity.
      eapply normalize_sound_fwd; eauto using notsInList_true.

      Lemma formals_grab : forall V x xs fE,
        In x xs
        -> formals V xs fE (x ++ "0")%string = Dyn (sel V x).
      Proof.
        induction xs; simpl; intuition (subst; eauto).
        unfold fo_set.
        destruct (string_dec (x ++ "0")%string (x ++ "0")%string); subst; congruence.
        unfold fo_set.
        destruct (string_dec (x ++ "0")%string (a ++ "0")%string); subst; auto.
        apply append0_invert in e; subst.
        auto.
      Qed.

      Lemma vars_ok_formals : forall V xs fE,
        vars_ok (formals V xs fE) V (vars0 xs).
      Proof.
        unfold vars_ok, vars0; induction xs; simpl; intuition.

        destruct (string_dec a x); subst.
        injection H; clear H; intros; subst; simpl.
        unfold fo_set.
        destruct (string_dec (x ++ "0") (x ++ "0")); tauto.
        destruct (in_dec string_dec x xs); try discriminate.
        injection H; clear H; intros; subst; simpl.
        unfold fo_set.
        destruct (string_dec (x ++ "0") (a ++ "0")).
        apply append0_invert in e; congruence.
        auto using formals_grab.
      Qed.

      apply vars_ok_formals.
      step auto_ext.
      step auto_ext.
      descend; step auto_ext.
      rewrite sel_eta.
      descend; step auto_ext.
      descend; step auto_ext.
      eapply normalize_sound_bwd; eauto using notsInList_true.


      hnf; auto.
      intros.
      apply in_app_or in H; intuition eauto using in_or_app.
      apply in_or_app; right; simpl; tauto.

      apply in_app_or in H0; intuition eauto using in_or_app, In_notInList.
      simpl in H; intuition (subst; eauto using in_or_app, In_notInList).
      discriminate.

      rewrite Hndts in *; auto.

      unfold vars0 in *.
      destruct (in_dec string_dec x (Formals a)); auto; try congruence.
      injection H; clear H; intros; subst; simpl.
      apply H20.
      apply in_or_app; left.
      apply in_map_iff; eauto using in_or_app.

      eauto using notsInList_true.

      apply good_vars_sound in H14.
      eapply Forall_forall in H14; eauto.

      subst.
      eapply notsInList_true in H15.
      tauto.
      eauto.
      simpl; tauto.

      apply in_app_or in H25; intuition idtac.
      apply in_map_iff in H20; destruct H20; intuition subst.
      apply in_app_or in H27; intuition idtac.
      eapply notsInList_true in H15.
      tauto.
      apply H.
      right.
      apply in_or_app; left.
      apply in_map_iff.
      eauto using in_or_app.
      eapply notsInList_true in H15.
      tauto.
      apply H.
      right.
      apply in_or_app; left.
      apply in_map_iff.
      eauto using in_or_app.
      eapply notsInList_true in H15.
      tauto.
      apply H.
      right.
      apply in_or_app; auto.

      apply good_vars_sound in H13.
      eapply Forall_forall in H13; eauto.

      apply in_app_or in H0; intuition idtac.
      apply in_map_iff in H; destruct H; intuition subst.
      assert (anyZero (x ++ "0")%string = true) by apply anyZero_duh.
      rewrite H0 in H.
      discriminate.

      eauto using In_notInList.

      eapply In_notInList; eauto.

      eapply In_notInList; eauto.

      apply in_app_or in H0; intuition eauto using In_notInList.
      apply in_map_iff in H; destruct H; intuition subst.
      assert (anyZero (x ++ "0")%string = true) by apply anyZero_duh.
      rewrite H0 in H.
      discriminate.

      rewrite Hndts in *; assumption.

      apply LabelMap.find_1.

      Lemma MapsTo_fullImports' : forall m m' f sp (fs0 : list (StructuredModule.function m'))
                                        (acc : LabelMap.t assert),
        m <> m'
        -> LabelMap.MapsTo (labl m f) sp acc
        -> LabelMap.MapsTo (labl m f) sp (List.fold_left (fun m p => let '(f, pre, _) := p in
           LabelMap.add (m', Global f) pre m) fs0 acc).
      Proof.
        induction fs0; simpl; intuition.
        destruct a as [ [ ] ]; simpl in *.
        eauto.
      Qed.

      Lemma MapsTo_fullImports : forall m m' f sp imps fs0,
        m <> m'
        -> LabelMap.MapsTo (labl m f) sp (importsMap imps)
        -> LabelMap.MapsTo (labl m f) sp (fullImports (modName := m') imps fs0).
      Proof.
        intros; apply MapsTo_fullImports'; auto.
      Qed.

      apply MapsTo_fullImports; auto.
      apply LabelMap.add_1; reflexivity.

      apply in_or_app; simpl; tauto.

      apply in_app_or in H0; intuition idtac.
      apply good_vars_sound in H12.
      eapply Forall_forall in H12; eauto.
      destruct H12.
      apply good_vars_sound in H11.
      eapply Forall_forall in H11; eauto.
      destruct H11.

      unfold vars0.
      destruct (in_dec string_dec "_" (Formals a)); auto.
      apply good_vars_sound in H12.
      eapply Forall_forall in H12; eauto.
      destruct H12.    
    Qed.
  End dts'.

  Let dts' := map normalizeDatatype dts.

  (** * Modules *)

  (** A named group of functions *)
  Record module := {
    MName : string;
    Functions : list function
  }.

  (** Generating a full module *)
  Section compileModule.
    Variable m : module.

    Definition compileModule : XCAP.module :=
      bmodule_ (("malloc", "malloc", Programming.Precondition mallocS None) :: nil)
               (MName m) (map compileFunction (Functions m)).

    Lemma preserve_None : forall fs,
      fold_left
      (fun (mOpt : option (LabelMap.t unit)) (f : function) =>
        match mOpt with
          | Some mp =>
            if LabelMap.mem (elt:=unit) (Name f, Local 0) mp
              then None
              else Some (LabelMap.add (Name f, Local 0) tt mp)
          | None => None
        end) fs None = None.
    Proof.
      induction fs; simpl; intuition.
    Qed.

    Theorem NoDupFunc_out : forall fs (mp : LabelMap.t unit),
      match (List.fold_left (fun mOpt f =>
        match mOpt with
          | None => None
          | Some mp => let k := (Name f, Local 0) in
            if LabelMap.mem k mp then None
              else Some (LabelMap.add k tt mp)
        end) fs (Some mp)) with
        | None => False
        | Some _ => True
      end
      -> match (List.fold_left (fun mOpt (p : StructuredModule.function (MName m)) => let '(modl, _, _) := p in
        match mOpt with
          | None => None
          | Some m => let k := (modl, Local 0) in
            if LabelMap.mem k m then None
              else Some (LabelMap.add k tt m)
        end) (map (fun p => match p with
                              | {| FName := f; FVars := ns; FReserved := res;
                                FPrecondition := pre; FBody := ch |} =>
                              (f, pre, fun im' H => toCmd ch (MName m) H ns res)
                            end)
        (map compileFunction fs)) (Some mp)) with
           | None => False
           | Some _ => True
         end.
    Proof.
      induction fs as [ | [ ] ]; simpl; intuition.

      unfold compileFunction; simpl.
      destruct (boundVars Precondition0); simpl.
      destruct (boundVars Postcondition0); simpl.
      destruct (LabelMap.mem (Name0, Local 0) mp).
      rewrite preserve_None in *; tauto.
      apply IHfs; auto.
      destruct (LabelMap.mem (Name0, Local 0) mp).
      rewrite preserve_None in *; tauto.
      apply IHfs; auto.
      destruct (LabelMap.mem (Name0, Local 0) mp).
      rewrite preserve_None in *; tauto.
      apply IHfs; auto.
    Qed.

    Hypothesis NoDupFunc :
      match (List.fold_left (fun mOpt f =>
        match mOpt with
          | None => None
          | Some mp => let k := (Name f, Local 0) in
            if LabelMap.mem k mp then None
            else Some (LabelMap.add k tt mp)
        end) (Functions m) (Some (LabelMap.empty unit))) with
        | None => False
        | Some _ => True
      end.

    Hypothesis Hnodup : nodup dts.
    Hypothesis Hndts : ndts_good dts dts'.
    Hypothesis Hdts : datatypesWf dts.

    Hypothesis FuncsWf : functionsWf (Functions m) = true.
    Hypothesis FuncsVcs : vcs (makeVcs dts' (Functions m)).
    Hypothesis ModName : MName m <> "malloc".

    (** Final correctness theorem *)
    Theorem compileModule_ok : moduleOk compileModule.
    Proof.
      intros; apply bmoduleOk; auto.

      Opaque string_dec.
      simpl.
      destruct (string_dec "malloc" (MName m)); congruence.

      apply NoDupFunc_out; auto.

      eapply makeVcs_correct; eauto.
    Qed.
  End compileModule.
End dts.
