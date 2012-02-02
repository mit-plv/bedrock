Require Import List.
Require Import Bedrock.ndep.Expr.
Require Import EquivDec.
Require Import DepList.

Set Implicit Arguments.

Notation "[ a ]" := (a :: nil).
Notation "[ a ,  b ]" := (a :: b :: nil).
Notation "[ a ,  b ,  c ]" := (a :: b :: c :: nil).
Notation "[ a ,  b ,  c ,  d ]" := (a :: b :: c :: d :: nil).

Section ProverT.
  Variable types : list type.
  Variable fs : functions types.

(*
  Definition ProverT : Type := forall 
    (hyps : list (@expr types))
    (goal : @expr types),
    AllProvable fs nil nil hyps ->
    option (Provable fs nil nil goal).
  (* It actually might be more correct for this to be 
   * option (AllProvable fs nil nil hyps -> Provable fs nil nil goal) 
   * but that is harder to program with
   *)
*)

  Definition ValidProp (e : expr types) := ~ exprD fs nil nil e tvProp = None.

  Lemma Provable_ValidProp : forall goal, Provable fs nil nil goal -> ValidProp goal.
    intros.
    unfold Provable, ValidProp in *.
    destruct (exprD fs nil nil goal tvProp); intuition.
    discriminate.
  Qed.
  
  Definition ProverCorrect (prover : list (@expr types) -> @expr types -> bool) :=
    forall hyps goal, prover hyps goal = true ->
      ValidProp goal ->
      AllProvable fs nil nil hyps ->
      Provable fs nil nil goal.

  (* the non-dependent prover should be *)
  Record NProverT : Type :=
  {
    prove : forall (hyps : list (@expr types)) (goal : @expr types), bool;
    prove_correct : ProverCorrect prove
  }.

End ProverT.

Definition eq_dec_to_seq_dec A (d : forall x y : A, { x = y } + { ~ x = y }) x y : option (x = y)
  := match (d x y) with
       | left pf => Some pf
       | right _ => None
     end.

Require Import Arith Bool.
Definition type_nat := {| Expr.Eq := eq_dec_to_seq_dec eq_nat_dec |}.
Definition type_bool := {| Expr.Eq := eq_dec_to_seq_dec bool_dec |}.
Definition type_list_bool := {| Expr.Eq := eq_dec_to_seq_dec (list_eq_dec bool_dec) |}.
Definition test_types := [type_nat, type_bool, type_list_bool].
(* 0 => nat, 1 => bool, 2 => list bool *)
Definition tvar_nat := tvType 0.
Definition tvar_bool := tvType 1.
Definition tvar_list_bool := tvType 2.
Definition tvar_empty := tvType 3.
Definition test_eq_sig := Sig test_types [tvar_nat, tvar_nat] tvar_bool beq_nat.
Definition test_plus_sig := Sig test_types [tvar_nat, tvar_nat] tvar_nat plus.
Fixpoint bin_to_nat (ls : list bool) : nat :=
  match ls with
    | nil => 0
    | false :: ls' => 2 * (bin_to_nat ls')
    | true :: ls' => S (2 * (bin_to_nat ls'))
  end.
Definition test_bin_to_nat_sig := Sig test_types [tvar_list_bool] tvar_nat bin_to_nat.
Definition test_constant_false_sig := Sig test_types [tvar_empty] tvar_bool (fun _ => false).
Definition test_functions := [test_eq_sig, test_plus_sig, test_bin_to_nat_sig, test_constant_false_sig].
(* 0 => eq, 1 => plus, 2 => bin_to_nat, 3 => fun _ => false *)
Eval compute in (Denotation test_eq_sig).
Eval compute in (functionTypeD (map (tvarD test_types) (Domain test_eq_sig))
         (tvarD test_types (Range test_eq_sig))).

Hint Unfold ProverCorrect ValidProp Provable : provers.
Ltac prover2 := intros; autounfold with provers in *; intros;
  match goal with
    | [ hyps : list (@expr _) |- _ ] => induction hyps
  end; simpl in *; try discriminate;
  match goal with
    | _ => pose 4
  end.

Section AssumptionProver.
  Variable types : list type.
  Variable fs : functions types.

  Fixpoint assumptionProver (hyps : list (expr types)) (goal : expr types) : bool :=
    match hyps with
      | nil => false
      | exp :: b => if seq_dec exp goal then true else false
    end.

  Theorem assumptionProverCorrect : ProverCorrect fs assumptionProver.
    prover2.
    destruct (expr_seq_dec a goal).
    subst.
    intuition.
    discriminate.
  Qed.

  Definition assumptionProverRec := {| prove := assumptionProver; prove_correct := assumptionProverCorrect |}.
End AssumptionProver.

Section UpdatePosition.
  Variable A : Type.
  
  Fixpoint updatePosition (ls : list A) (n : nat) (new : A) : list A :=
    match ls with
      | nil => match n with
                 | 0 => [new]
                 | S n' => new :: updatePosition nil n' new
               end
      | a :: ls' => match n with
                      | 0 => new :: ls'
                      | S n' => a :: updatePosition ls' n' new
                    end
    end.

  Require Import Omega.
  Hint Resolve lt_n_O.
  Lemma nth_error_updatePosition_nil : forall (new : A) n, nth_error (updatePosition nil n new) n = value new.
    intros.
    induction n; auto.
  Qed.
  Hint Resolve nth_error_updatePosition_nil.
  Lemma nth_error_updatePosition : forall (new : A) ls n, nth_error (updatePosition ls n new) n = value new.
    intro.
    double induction ls n; auto.
    intros.
    specialize (H0 H).
    simpl.
    destruct l0; auto.
  Qed.
End UpdatePosition.

Ltac caseDestruct t := destruct t; try discriminate.

Ltac dintuition := repeat (intuition;
  match goal with
    | [ H : exists _, _ |- _ ] => destruct H
  end).

Ltac hypRewriter := repeat match goal with
                             | [ H : _ = _ |- _] => rewrite H
                           end.
Ltac unlet := repeat match goal with
                       | [ x := ?y |- _ ] => subst x
                     end.

Ltac provers := unlet; repeat (repeat (autorewrite with provers in *; hypRewriter); simpl in *; subst; dintuition); try congruence; firstorder.

Section ReflexivityProver.
  Context {types : list type}.
  Variable fs : functions types.
  Variable eqFunIdx : func.
  Variable eqFunTvar : tvar.

  Let eqFunSig := {| Domain := [eqFunTvar, eqFunTvar]; Range := tvProp; Denotation := (@eq (tvarD types eqFunTvar)) |}.
  Let fs' := updatePosition fs eqFunIdx eqFunSig.

  Definition reflexivityProver (hyps : list (expr types)) (goal : expr types) := 
    match goal with
      | Func f [x, y] => if equiv_dec f eqFunIdx
                           then if expr_seq_dec x y then true else false
                           else false
      | _ => false
    end.

  Hint Rewrite nth_error_updatePosition : provers.
  Theorem reflexivityProverCorrect : ProverCorrect fs' reflexivityProver.
    unfold ProverCorrect; intros.
    caseDestruct goal.
    repeat caseDestruct l.
    simpl in *.
    caseDestruct (equiv_dec f eqFunIdx).
    unfold equiv in *.
    caseDestruct (expr_seq_dec e e0).
    subst.
    unfold fs', exprD, Provable.
    simpl.
    rewrite nth_error_updatePosition.
    simpl.
    unfold ValidProp in *.
    unfold fs' in *.
    case_eq (exprD (updatePosition fs eqFunIdx eqFunSig) nil nil e0 eqFunTvar); intros.
    reflexivity.
    apply H0.
    provers.
  Qed.

  Definition reflexivityProverRec := {| prove := reflexivityProver; prove_correct := reflexivityProverCorrect |}.
End ReflexivityProver.

(* Algorithm for grouping expressions by equalities. Terribly inefficient... *)
Section Grouper.
  Variable A : Type.
  Variable A_seq_dec : forall (x y : A), option (x = y).
  
  Definition in_seq_dec (ls : list A) (a : A) : option (In a ls).
    induction ls.
    right.
    simpl.
    destruct IHls.
    left.
    tauto.
    destruct (A_seq_dec a0 a).
    left.
    tauto.
    right.
  Defined.

  Fixpoint groupWith (grps : list (list A)) (g : list A) (a : A) :=
    match grps with
      | nil => [g]
      | g' :: grps' => if in_seq_dec g' a
                         then groupWith grps' (g' ++ g) a
                         else g' :: groupWith grps' g a
    end.

  Fixpoint addEquality (ls : list (list A)) (a : A) (b : A) : list (list A) :=
    match ls with
      | nil => [[a]] (* matched nothing *)
      | grp :: ls' => if in_seq_dec grp a
                        then groupWith ls' grp b
                        else if in_seq_dec grp b
                               then groupWith ls' grp a
                               else grp :: addEquality ls' a b
    end.

  Fixpoint inSameGroup (grps : list (list A)) (a : A) (b : A) :=
    if A_seq_dec a b
      then true
      else
        match grps with
          | nil => false
          | g :: grps' => if in_seq_dec g a
                            then
                              if in_seq_dec g b
                                then true
                                else inSameGroup grps' a b
                            else inSameGroup grps' a b
        end.    

  Fixpoint groupEqualTo (g : list A) a :=
    match g with
      | nil => True
      | a' :: g' => a = a' /\ groupEqualTo g' a
    end.

  Lemma groupEqualTo_spec : forall (g : list A) a, groupEqualTo g a <-> (forall x, In x g -> a = x).
    intros; split; induction g; simpl in *; intuition; try congruence.
  Qed.
    
  Definition groupEqual (g : list A) :=
    match g with
      | nil => True
      | a' :: g' => groupEqualTo g' a'
    end.

  Lemma groupEqualTo_groupEqual : forall (g : list A) a, groupEqualTo g a -> groupEqual g.
    induction g; simpl in *; intuition; subst; intuition.
  Qed.

  Hint Resolve groupEqualTo_groupEqual.
  Lemma groupEqual_spec : forall (g : list A), groupEqual g <-> forall x y, In x g -> In y g -> x = y.
    intros; split; intros.
    induction g.
    intuition.
    simpl in *.
    destruct (groupEqualTo_spec g a).
    intuition.
    congruence.
    specialize (H1 _ H0); congruence.
    specialize (H1 _ H4); congruence.
    pose groupEqualTo_groupEqual.
    firstorder.
    induction g.
    provers.
    simpl in *; intuition.
    apply groupEqualTo_spec.
    intuition.
  Qed.

  Lemma groupEqual_app : forall g1 g2, groupEqual g1 -> groupEqual g2 -> (exists a, In a g1 /\ In a g2) -> groupEqual (g1 ++ g2).
    intros ? ? Hg1 Hg2 Hex.
    apply groupEqual_spec.
    destruct Hex.
    intuition.
    destruct (groupEqual_spec g1), (groupEqual_spec g2).
    repeat match goal with
      | [ H : In _ (_ ++ _) |- _ ] => destruct (in_app_or _ _ _ H); clear H
    end; intuition;
    repeat match goal with
      | [ H1 : In ?x ?g, H2 : In ?y ?g, H3 : groupEqual ?g |- _ ] =>
          match goal with
            | [ H : x = y |- _ ] => fail 1
            | [ H : y = x |- _ ] => fail 1
            | _ => assert (x = y) by intuition
          end
    end; congruence.
  Qed.

  Fixpoint groupsEqual (grps : list (list A)) :=
    match grps with
      | nil => True
      | g :: grps' => groupEqual g /\ groupsEqual grps'
    end.

  Ltac solve_spec := repeat (simpl in *; subst; intuition); try congruence; firstorder.
  
  Lemma groupsEqual_spec : forall (grps : list (list A)), groupsEqual grps <-> forall g, In g grps -> forall x y, In x g -> In y g -> x = y.
    induction grps; pose groupEqual_spec; solve_spec.
  Qed.

  Lemma groupsEqual_groupWith : forall grps, groupsEqual grps -> forall g, groupEqual g -> forall a, In a g -> groupsEqual (groupWith grps g a).
    induction grps; simpl in *; intuition.
    destruct (in_seq_dec a a0).
    apply H.
    apply groupEqual_app; firstorder.
    Hint Resolve in_or_app.
    eauto.
    simpl in *; intuition.
  Qed.

  Lemma groupsEqual_addEquality : forall grps, groupsEqual grps -> forall x y, x = y -> groupsEqual (addEquality grps x y).
    induction grps; solve_spec.
    case_eq (in_seq_dec a y); intros.
    apply groupsEqual_groupWith; solve_spec.
    solve_spec.
  Qed.

  Lemma inSameGroup_spec : forall x y grps, inSameGroup grps x y = true <-> (exists pf, A_seq_dec x y = Some pf) \/ exists g, In g grps /\ (exists pfx, in_seq_dec g x = Some pfx) /\ (exists pfy, in_seq_dec g y = Some pfy).
    solve_spec.
    case_eq (A_seq_dec x y); intros.
    left.
    exists e; reflexivity.
    right.
    induction grps.
    simpl in *.
    rewrite H0 in H.
    intuition.
    simpl in *.
    rewrite H0 in H.
    case_eq (in_seq_dec a x); intros; rewrite H1 in H.
    case_eq (in_seq_dec a y); intros; rewrite H2 in H.
    firstorder.
    firstorder.
    firstorder.
    destruct grps; simpl in *; rewrite H; intuition.
    induction grps; simpl in *; intuition;
    case_eq (A_seq_dec x y); intuition; subst.
    rewrite H0, H1; intuition.
    destruct (in_seq_dec a x); destruct (in_seq_dec a y); intuition.
  Qed.

  Lemma inSameGroup_addEquality : forall x y grps, A_seq_dec x y <> None -> inSameGroup (addEquality grps x y) x y = true.
    intros.
    case_eq (A_seq_dec x y); intuition.
    subst.
    induction grps.
    simpl; intuition.
    repeat rewrite H0; intuition.
    destruct (addEquality (a :: grps) y y); simpl; rewrite H0; intuition.
  Qed.

  Lemma in_seq_dec_spec : forall x g, (exists pf, in_seq_dec g x = Some pf) <-> In x g /\ exists pf, A_seq_dec x x = Some pf.
    dintuition.
    induction g; intuition.
    simpl in *; intuition.
    destruct x0; intuition.
    subst.
    destruct (in_seq_dec g x); intuition.
    apply (IHg i); intuition.
    destruct (A_seq_dec x x); intuition.
    exists e; intuition.
    discriminate.
    destruct (in_seq_dec g x).
    apply (IHg i0); intuition.
    case_eq (A_seq_dec a x); intros.
    subst.
    rewrite H0.
    exists eq_refl.
    reflexivity.
    rewrite H0 in H.
    discriminate.
    induction g.
    intuition.
    simpl in *; intuition.
    destruct (in_seq_dec g x).
    exists (or_intror (a = x) i); reflexivity.
    subst.
    exists (or_introl (In x g) x0).
    rewrite H; reflexivity.
    dintuition.
    rewrite H0.
    exists (or_intror (a = x) x1).
    reflexivity.
  Qed.
    
  Lemma in_seq_dec_app : forall x g g', (exists pfl, in_seq_dec g x = Some pfl) -> exists pfr, in_seq_dec (g' ++ g) x = Some pfr.
    dintuition.
    induction g'.
    simpl in *; firstorder.
    simpl in *.
    destruct IHg'.
    rewrite H0.
    exists (or_intror (a = x) x1); intuition.
  Qed.

  Lemma in_seq_dec_app_r : forall x g g', (exists pfl, in_seq_dec g x = Some pfl) -> exists pfr, in_seq_dec (g ++ g') x = Some pfr.
    intros.
    apply in_seq_dec_app with (g' := g') in H.
    pose in_seq_dec_spec.
    destruct (i x (g' ++ g)).
    apply in_seq_dec_spec.
    intuition.
    apply in_or_app.
    apply in_app_or in H0.
    intuition.
  Qed.

  Lemma in_impl_in_seq_dec_impl : forall g g', (forall y, In y g -> In y g') -> forall y, (exists pf, in_seq_dec g y = Some pf) -> exists pf', in_seq_dec g' y = Some pf'.
    intros.
    apply in_seq_dec_spec.
    destruct (in_seq_dec_spec y g).
    solve_spec.
  Qed.

  Lemma groupWith_spec1 : forall grps g, In g grps -> forall x, in_seq_dec g x = None -> forall g', In g (groupWith grps g' x).
    induction grps; solve_spec.
    rewrite H; solve_spec.
    destruct (in_seq_dec a x); solve_spec.
  Qed.

  Lemma groupWith_last : forall grps g x y, In y g -> In y (last (groupWith grps g x) nil).
    induction grps; solve_spec.
    destruct (in_seq_dec a x).
    intuition.
    simpl.
    specialize (IHgrps g x y).
    destruct (groupWith grps g x); simpl in *; intuition.
  Qed.

  Lemma groupWith_last_in_seq_dec : forall grps g x y, (exists pf, in_seq_dec g y = Some pf) -> exists pf, in_seq_dec (last (groupWith grps g x) nil) y = Some pf.
    induction grps; solve_spec.
    destruct (IHgrps g x y (ex_intro _ _ H)).
    apply in_seq_dec_spec; intuition.
    destruct (in_seq_dec a x).
    apply groupWith_last.
    solve_spec.
    solve_spec.
    destruct (groupWith grps g x); solve_spec.
    destruct (in_seq_dec_spec y g).
    solve_spec.
  Qed.

  Lemma groupWith_nil : forall grps g x, groupWith grps g x <> nil.
    induction grps; solve_spec.
    destruct (in_seq_dec a x); solve_spec.
  Qed.

  Lemma last_in : forall B (l : list B) b, l <> nil -> In (last l b) l.
    induction l; solve_spec.
    destruct l.
    solve_spec.
    right.
    apply IHl.
    solve_spec.
  Qed.

  Lemma groupWith_spec2 : forall grps g, In g grps -> forall x, (exists pf, in_seq_dec g x = Some pf) -> forall g1, exists g', In g' (groupWith grps g1 x) /\  forall y, In y g -> In y g'.
    intros.
    exists (last (groupWith grps g1 x) nil).
    solve_spec.
    case_eq (groupWith grps g1 x); intros.
    apply groupWith_nil in H1; intuition.
    apply last_in; solve_spec.
    revert grps g H x g1 y H1 x0 H0.
    induction grps.
    solve_spec.
    intros.
    simpl in *; intuition.
    subst.
    rewrite H0.
    apply groupWith_last; solve_spec.
    destruct (in_seq_dec a x).
    eapply IHgrps; eauto.
    simpl.
    case_eq (groupWith grps g1 x); intros.
    apply groupWith_nil in H; intuition.
    rewrite <- H.
    eapply IHgrps; eauto.
  Qed.

  Lemma groupWith_groups : forall grps g, In g grps -> forall g1 x, exists g2, In g2 (groupWith grps g1 x) /\ (forall y, In y g -> In y g2).
    intros.
    case_eq (in_seq_dec g x); intros.
    apply groupWith_spec2; solve_spec.
    exists g; split.
    apply groupWith_spec1; solve_spec.
    solve_spec.
  Qed.

  Hint Resolve last_in groupWith_nil groupWith_last.
  Lemma groupWith_arg : forall grps g x, exists g', In g' (groupWith grps g x) /\ forall y, In y g -> In y g'.
    intros.
    exists (last (groupWith grps g x) nil); intuition eauto.
  Qed.

  Hint Rewrite plus_assoc : null.
  Lemma inSameGroup_refl : forall grps x, (exists pf, A_seq_dec x x = Some pf) -> inSameGroup grps x x = true.
    induction grps; solve_spec; rewrite H; reflexivity.
  Qed.
    
  Hint Resolve groupWith_last_in_seq_dec in_seq_dec_app_r.
  Lemma inSameGroup_groupWith : forall grps x y, inSameGroup grps x y = true -> forall g z, inSameGroup (groupWith grps g z) x y = true.
    intros.
    apply inSameGroup_spec.
    case_eq (A_seq_dec x y); intros; [ left | right ].
    exists e; solve_spec.
    revert grps x y H g z H0.
    induction grps; intuition;
    simpl in *;
    rewrite H0 in H; intuition.
    case_eq (in_seq_dec a z); intros.
    case_eq (in_seq_dec a x); intros;
    rewrite H2 in *.
    case_eq (in_seq_dec a y); intros;
    rewrite H3 in *.
    exists (last (groupWith grps (a ++ g) z) nil); intuition;
    apply (groupWith_last_in_seq_dec);
    apply in_seq_dec_app_r; firstorder.
    intuition eauto.
    intuition eauto.
    case_eq (in_seq_dec a x); intros.
    case_eq (in_seq_dec a y); intros.
    exists a.
    solve_spec.
    rewrite H2, H3 in *.
    destruct (IHgrps x y H g z); try assumption.
    solve_spec.
    rewrite H2 in *.
    destruct (IHgrps x y H g z); try assumption.
    solve_spec.
  Qed.

  Hint Resolve inSameGroup_groupWith in_impl_in_seq_dec_impl.
  Theorem inSameGroup_addEquality_preserved : forall x y grps, inSameGroup grps x y = true -> forall w z, inSameGroup (addEquality grps w z) x y = true.
    induction grps; solve_spec.
    destruct (A_seq_dec x y); solve_spec.
    case_eq (A_seq_dec x y); intros.
    match goal with
      | [ |- inSameGroup ?l _ _ = true ] => destruct l
    end; solve_spec; rewrite H0 in *; intuition.
    rewrite H0 in *.
    case_eq (in_seq_dec a x); intros;
    rewrite H1 in *.
    case_eq (in_seq_dec a y); intros;
    rewrite H2 in *.
    case_eq (in_seq_dec a w); intros.
    apply inSameGroup_spec.
    right.
    destruct (groupWith_arg grps a z).
    exists x0.
    intuition eauto.
    destruct (in_seq_dec a z).
    apply inSameGroup_spec.
    right.
    destruct (groupWith_arg grps a w).
    exists x0.
    intuition eauto.
    simpl.
    rewrite H0, H1, H2; reflexivity.
    destruct (in_seq_dec a w).
    eauto.
    destruct (in_seq_dec a z).
    eauto.
    simpl.
    rewrite H0, H1, H2.
    eauto.
    destruct (in_seq_dec a w).
    eauto.
    destruct (in_seq_dec a z).
    eauto.
    simpl.
    rewrite H0, H1.
    eauto.
  Qed.
End Grouper.

Section BabyOmega.
  Hint Rewrite nth_error_updatePosition : provers.
  
  Variable types : list type.
  Variable natIdx : nat.
  Let natType := {| Expr.Eq := eq_dec_to_seq_dec eq_nat_dec |}.
  Let types' := updatePosition types natIdx natType.
  Variable fs : functions types'.
  Variable eqFunIdx : nat.
  Let natTvar := tvType natIdx.
  
  Let eqFunSig := {| Domain := [natTvar, natTvar]; Range := tvProp; Denotation := (@eq (tvarD types' natTvar)) |}.
  Let fs' := updatePosition fs eqFunIdx eqFunSig.

  (*Fixpoint cast' (P : option type -> Type) natIdx types : P (nth_error types' natIdx) -> P (Some natType) :=
  match natIdx with
    | O => fun x => x
    | S natIdx' => match types
                     return P (nth_error (updatePosition types (S natIdx') natType)
                       (S natIdx')) -> _ with
                     | nil => cast' P natIdx' nil
                     | _ => cast' P natIdx' _
                   end
  end.*)
  

  Definition nat_seq_dec := eq_dec_to_seq_dec eq_nat_dec.
  
  Definition optionDefault T (o : option T) t :=
    match o with
      | Some pf => pf
      | None => t
    end.

  Definition natTvarCoerce (n : nat) : tvarD types' natTvar.
    simpl.
    subst types'.
    rewrite nth_error_updatePosition.
    simpl.
    exact n.
  Defined.

  Lemma nth_error_types'_natIdx : nth_error types' natIdx = value {| Expr.Eq := eq_dec_to_seq_dec eq_nat_dec |}.
    provers.
  Qed.
  Hint Rewrite nth_error_types'_natIdx : provers.
  
  Definition natTvarCoerceR (n : tvarD types' natTvar) : nat.
    simpl in *.
    rewrite nth_error_types'_natIdx in *.
    simpl in *.
    exact n.
  Defined.

  (*Lemma natTvarCoerceR_natTvarCoerce : forall n, natTvarCoerceR (natTvarCoerce n) = n.
    induction n.
    unfold natTvarCoerce.
    unfold eq_rect_r, eq_rect.
    generalize (nth_error (updatePosition types natIdx
           {| Impl := nat; Expr.Eq := eq_dec_to_seq_dec eq_nat_dec |}) natIdx).
    generalize (Logic.eq_sym
         (nth_error_updatePosition
            {| Impl := nat; Expr.Eq := eq_dec_to_seq_dec eq_nat_dec |} types
            natIdx)).
    intro.

    case e.
    generalize {| Impl := nat; Expr.Eq := eq_dec_to_seq_dec eq_nat_dec |}.
    intro.
    destruct e.
    rewrite nth_error_updatePosition.
    pose (NatEqdep.UIP_refl 0).*)

  Lemma natTvarCoerceR_inj : forall m n, natTvarCoerceR m = natTvarCoerceR n -> m = n.
  Admitted.
    (*simpl in *.
    unfold natTvarCoerceR in H.
    assert (match nth_error types' natIdx with
      | Some t => Impl t
      | None => Empty_set
      end = nat) by provers.
    simpl in H.
    rewrite H0 in H.
    elim (nth_error types' natIdx).*)

  Definition enD (e : expr types') := natTvarCoerceR (optionDefault (exprD fs' nil nil e natTvar) (natTvarCoerce O)).
 
  Lemma eq_nat_dec_correct : forall n, eq_nat_dec n n = left eq_refl.
    induction n; provers.
  Qed.
  Hint Rewrite eq_nat_dec_correct : provers.

  Lemma nat_seq_dec_correct : forall n, nat_seq_dec n n = Some eq_refl.
    unfold nat_seq_dec, eq_dec_to_seq_dec in *.
    provers.
    autorewrite with provers in *.
    provers.
  Qed.
  Hint Rewrite nat_seq_dec_correct : provers.

  Fixpoint eqGrouper (hyps : list (expr types')) :=
      match hyps with
        | nil => nil
        | hyp :: hyps' => match hyp with
                            | Func f [x, y] => if eq_nat_dec f eqFunIdx
                                                 then addEquality (@nat_seq_dec) (eqGrouper hyps') (enD x) (enD y)
                                                 else eqGrouper hyps'
                            | _ => eqGrouper hyps'
                          end
      end.

  Hint Rewrite inSameGroup_addEquality : provers.
  Lemma eqGrouper_spec : forall hyps x y, (exists pf, expr_seq_dec x y = Some pf) -> In (Func eqFunIdx [x, y]) hyps -> inSameGroup nat_seq_dec (eqGrouper hyps) (enD x) (enD y) = true.
    intros.
    induction hyps; intuition.
    simpl in *.
    destruct H, H0.
    provers.
    destruct a; intuition.
    repeat (destruct l; intuition).
    destruct (eq_nat_dec f eqFunIdx); intuition.
    apply inSameGroup_addEquality_preserved.
    assumption.
  Qed.
  
  Lemma eqFunIdx_eq : forall e e', ValidProp fs' (Func eqFunIdx [e, e']) -> exprD fs' nil nil (Func eqFunIdx [e,  e']) tvProp = Some (optionDefault (exprD fs' nil nil e natTvar) (natTvarCoerce 0) = optionDefault (exprD fs' nil nil e' natTvar) (natTvarCoerce 0)).
    intros.
    simpl.
    subst fs'.
    unfold ValidProp in H.
    repeat rewrite nth_error_updatePosition in *.
    simpl in *.
    repeat rewrite nth_error_updatePosition in *.
    simpl in *.
    caseDestruct (exprD (updatePosition fs eqFunIdx eqFunSig) nil nil e natTvar); intuition.
    caseDestruct (exprD (updatePosition fs eqFunIdx eqFunSig) nil nil e' natTvar); intuition.
  Qed.

  Lemma nth_error_fs'_eqFunIdx : nth_error fs' eqFunIdx = Some eqFunSig.
    provers.
  Qed.

  Lemma Provable_Func_eq : forall e e', Provable fs' nil nil (Func eqFunIdx [e, e']) -> exprD fs' nil nil e natTvar = exprD fs' nil nil e' natTvar.
    intros.
    unfold Provable in H.
    simpl in H.
    rewrite nth_error_fs'_eqFunIdx in *.
    simpl in *.
    destruct (exprD fs' nil nil e natTvar);
    destruct (exprD fs' nil nil e' natTvar);
      provers.
  Qed.

  Hint Resolve groupsEqual_addEquality Provable_Func_eq.
  Lemma eqGrouper_groupsEqual : forall hyps, AllProvable fs' nil nil hyps -> groupsEqual (eqGrouper hyps).
    intros.
    induction hyps; intuition.
    simpl.
    destruct a; simpl in *; intuition.
    repeat (destruct l; simpl in *; intuition).
    destruct (eq_nat_dec f eqFunIdx).
    pose (Provable_ValidProp _ _ H0).
    subst.
    pose (eqFunIdx_eq v).
    apply groupsEqual_addEquality.
    eauto.
    unfold enD.
    erewrite Provable_Func_eq; eauto.
    assumption.
  Qed.

  Definition transitivityProver (hyps : list (expr types')) (goal : expr types') :=
    match goal with
      | Func f [x, y] => if equiv_dec f eqFunIdx
                           then inSameGroup nat_seq_dec (eqGrouper hyps) (enD x) (enD y)
                           else false
      | _ => false
    end.

  Lemma natTvar_nat : tvarD types' natTvar = nat.
    provers.
  Qed.

  Ltac dintuition := repeat (intuition; match goal with
                                          | [ H : exists _, _ |- _ ] => destruct H
                                        end).
  Theorem transitivityProverCorrect : ProverCorrect fs' transitivityProver.
    unfold ProverCorrect; intros.
    unfold Provable, transitivityProver in *.
    caseDestruct goal.
    repeat caseDestruct l.
    caseDestruct (equiv_dec f eqFunIdx).
    unfold equiv in e1.
    subst.
    rewrite eqFunIdx_eq; eauto.
    edestruct inSameGroup_spec; clear H3.
    specialize (H2 H).
    apply eqGrouper_groupsEqual in H1.
    edestruct groupsEqual_spec; clear H4.
    specialize (H3 H1).
    unfold ValidProp in *.
    simpl in *.
    rewrite nth_error_fs'_eqFunIdx in H0.
    simpl in *.
    case_eq (exprD fs' nil nil e natTvar); intros; rewrite H4 in *.
    case_eq (exprD fs' nil nil e0 natTvar); intros; rewrite H5 in *.
    dintuition.
    simpl.
    unfold enD in *.
    clear H2.
    rewrite H4, H5 in x.
    simpl in *.
    apply natTvarCoerceR_inj; assumption.
    dintuition.
    simpl.
    specialize (H3 _ H6 _ _ x1 x0).
    unfold enD in H3.
    rewrite H4, H5 in *.
    simpl in *.
    apply natTvarCoerceR_inj.
    eauto.
    tauto.
    tauto.
  Qed.
End BabyOmega.
