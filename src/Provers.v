Require Import List Arith Bool.
Require Import Expr Env.
Require Import EquivDec EqdepClass.
Require Import DepList.

Set Implicit Arguments.

(* Coq supports recursive patterns *)
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

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

  Definition ValidProp (e : expr types) := exists pf, exprD fs nil nil e tvProp = Some pf.

  Lemma Provable_ValidProp : forall goal, Provable fs nil nil goal
    -> ValidProp goal.
    unfold Provable, ValidProp in *; intros;
      repeat match goal with
               | [ _ : match ?E with None => _ | Some _ => _ end |- _ ] =>
                 destruct E
             end; intuition eauto.
  Qed.

  Definition ProverCorrect
    (prover : list (@expr types) -> @expr types -> bool) :=
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

Definition nat_seq_dec : forall a b : nat, option (a = b) := seq_dec. 

Lemma eq_nat_dec_correct : forall n, eq_nat_dec n n = left eq_refl.
  induction n; provers.
Qed.
Hint Rewrite eq_nat_dec_correct : provers.

Lemma nat_seq_dec_correct : forall n, nat_seq_dec n n = Some eq_refl.
  unfold nat_seq_dec, seq_dec. provers.
Qed.
Hint Rewrite nat_seq_dec_correct : provers.

(* Some test cases for later, might remove *)
Definition type_nat := {| Expr.Impl := nat ; Expr.Eq := seq_dec |}.
Definition type_bool := {| Expr.Impl := bool ; Expr.Eq := seq_dec |}.
Definition type_list_bool := {| Expr.Impl := list bool ; Expr.Eq := seq_dec |}.
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
    | false :: ls' => 2 * bin_to_nat ls'
    | true :: ls' => S (2 * bin_to_nat ls')
  end.
Definition test_bin_to_nat_sig := Sig test_types [tvar_list_bool] tvar_nat bin_to_nat.
Definition test_constant_false_sig := Sig test_types [tvar_empty] tvar_bool (fun _ => false).
Definition test_functions := [test_eq_sig, test_plus_sig, test_bin_to_nat_sig, test_constant_false_sig].

Ltac caser H E := case_eq E; intros;
  try match goal with
        | [ H' : _ = _ |- _ ] => rewrite H' in H
      end.

(* Everything looks like a nail?  Try this hammer. *)
Ltac t1 := match goal with
             | _ => discriminate
             | _ => progress (hnf in *; simpl in *; intuition; subst)
             | [ x := _ : _ |- _ ] => subst x || (progress (unfold x in * ))
             | [ H : ex _ |- _ ] => destruct H
             | [ H : context[nth_error (updateAt ?new ?ls ?n) ?n] |- _ ] =>
               rewrite (nth_error_updateAt new ls n) in H
                 || rewrite nth_error_updateAt in H
             | [ s : signature _ |- _ ] => destruct s
             | [ H : Some _ = Some _ |- _ ] => injection H; clear H
             | [ H : _ = Some _ |- _ ] => rewrite H in *
             | [ H : _ === _ |- _ ] => rewrite H in *

             | [ |- context[match ?E with
                              | Const _ _ => _
                              | Var _ => _
                              | UVar _ => _
                              | Func _ _ => _
                            end] ] => destruct E
             | [ |- context[match ?E with
                              | None => _
                              | Some _ => _
                            end] ] => destruct E
             | [ |- context[if ?E then _ else _] ] => destruct E
             | [ |- context[match ?E with
                              | nil => _
                              | _ :: _ => _
                            end] ] => destruct E

             | [ _ : context[match ?E with
                               | Const _ _ => _
                               | Var _ => _
                               | UVar _ => _
                               | Func _ _ => _
                             end] |- _ ] => destruct E
             | [ _ : context[match ?E with
                               | nil => _
                               | _ :: _ => _
                             end] |- _ ] => destruct E
             | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
             | [ _ : context[match ?E with
                               | left _ => _
                               | right _ => _
                             end] |- _ ] => destruct E
             | [ _ : context[match ?E with
                               | tvProp => _
                               | tvType _ => _
                             end] |- _ ] => destruct E
             | [ _ : context[match ?E with
                               | None => _
                               | Some _ => _
                             end] |- _ ] => match E with
                                              | context[match ?E with
                                                          | None => _
                                                          | Some _ => _
                                                  end] => fail 1
                                              | _ => destruct E
                                            end
           end.

Ltac t := repeat t1; eauto.

Section AssumptionProver.
  Variable types : list type.
  Variable fs : functions types.

  Fixpoint assumptionProver (hyps : list (expr types))
    (goal : expr types) : bool :=
    match hyps with
      | nil => false
      | exp :: b => if expr_seq_dec exp goal
        then true
        else assumptionProver b goal
    end.

  Theorem assumptionProverCorrect : ProverCorrect fs assumptionProver.
    t; induction hyps; t.
  Qed.

  Definition assumptionProverRec := {|
    prove := assumptionProver;
    prove_correct := assumptionProverCorrect
  |}.
End AssumptionProver.

Section ReflexivityProver.
  Context {types : list type}.
  Variable fs : functions types.
  Variable eqFunIdx : func.
  Variable eqFunTvar : tvar.

  Let eqFunSig := {|
    Domain := [eqFunTvar, eqFunTvar];
    Range := tvProp;
    Denotation := @eq (tvarD types eqFunTvar)
  |}.
  Let fs' := updateAt eqFunSig fs eqFunIdx.

  Definition reflexivityProver (_ : list (expr types)) (goal : expr types) := 
    match goal with
      | Func f [x, y] => if equiv_dec f eqFunIdx
                           then if expr_seq_dec x y then true else false
                           else false
      | _ => false
    end.

  Theorem reflexivityProverCorrect : ProverCorrect fs' reflexivityProver.
    unfold reflexivityProver; t.
  Qed.

  Definition reflexivityProverRec := {|
    prove := reflexivityProver;
    prove_correct := reflexivityProverCorrect
  |}.
End ReflexivityProver.

(* Algorithm for grouping expressions by equalities. Terribly inefficient... *)
Section Grouper.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  (* An arbitrary equivalence relation
   * (though maybe we can get away without all the usual axioms) *)

  Hypothesis Rsym : forall x y, R x y -> R y x.
  Hypothesis Rtrans : forall x y z, R x y -> R y z -> R x z.

  Variable A_seq_dec : forall (x y : A), option (R x y).

  Fixpoint InR (x : A) (ls : list A) : Prop :=
    match ls with
      | nil => False
      | y :: ls' => R y x \/ InR x ls'
    end.

  Fixpoint in_seq_dec (ls : list A) (a : A) : option (InR a ls) :=
    match ls with
      | nil => None
      | x :: ls' =>
        match A_seq_dec x a with
          | None => match in_seq_dec ls' a with
                      | None => None
                      | Some pf => Some (or_intror _ pf)
                    end
          | Some pf => Some (or_introl _ pf)
        end
    end.

  Fixpoint groupWith (grps : list (list A)) (g : list A) (a : A) :=
    match grps with
      | nil => [g]
      | g' :: grps' => if in_seq_dec g' a
                         then (g' ++ g) :: grps'
                         else g' :: groupWith grps' g a
    end.

  Fixpoint addEquality (ls : list (list A)) (a : A) (b : A) : list (list A) :=
    match ls with
      | nil => [[a, b]] (* matched nothing *)
      | grp :: ls' => if in_seq_dec grp a
                        then groupWith ls' grp b
                        else if in_seq_dec grp b
                               then groupWith ls' grp a
                               else grp :: addEquality ls' a b
    end.

  Fixpoint inSameGroup (grps : list (list A)) (a : A) (b : A) :=
    match grps with
      | nil => false
      | g :: grps' => if in_seq_dec g a
        then
          if in_seq_dec g b
            then true
            else inSameGroup grps' a b
        else inSameGroup grps' a b
    end.

  Definition groupEqualTo (a : A) := Forall (R a).

  Definition groupEqual (g : list A) :=
    match g with
      | nil => True
      | a' :: g' => groupEqualTo a' g'
    end.

  Definition groupsEqual := Forall groupEqual.

  Hint Extern 1 (groupEqual _) => hnf.

  Hint Resolve Rsym Rtrans.

  Lemma Rweaken : forall x y l,
    Forall (R x) l
    -> R x y
    -> Forall (R y) l.
    induction 1; t.
  Qed.

  Hint Resolve Rweaken.

  Lemma groupEqualTo_groupEqual : forall x xs,
    Forall (R x) xs
    -> groupEqual xs.
    induction 1; t.
  Qed.

  Hint Resolve groupEqualTo_groupEqual.

  Lemma Forall_app : forall A (P : A -> Prop) ls1 ls2,
    Forall P ls1
    -> Forall P ls2
    -> Forall P (ls1 ++ ls2).
    induction 1; t.
  Qed.

  Hint Resolve Forall_app.

  Lemma groupEqualTo_In : forall x y g,
    InR y g
    -> Forall (R x) g
    -> R x y.
    induction 2; t.
  Qed.

  Hint Immediate groupEqualTo_In.

  Hint Extern 1 (Forall _ _) => progress hnf.

  Lemma groupWith_sound : forall x xs grps,
    Forall groupEqual grps
    -> Forall (R x) xs
    -> Forall groupEqual (groupWith grps xs x).
    induction 1; t; eauto 6.
  Qed.

  Hint Resolve groupWith_sound.

  Theorem addEquality_sound : forall x y grps,
    groupsEqual grps
    -> R x y
    -> groupsEqual (addEquality grps x y).
    induction 1; t; eauto 7.
  Qed.

  Theorem inSameGroup_sound : forall grps, groupsEqual grps
    -> forall x y, inSameGroup grps x y = true
      -> R x y.
    induction 1; t.
  Qed.
End Grouper.

Section TransitivityProver.
  Variable types : list type.
  Variable t : type.
  Variable tIdx : nat.

  Definition types' := updateAt t types tIdx.
  Let tTvar := tvType tIdx.

  Variable fs : functions types'.
  Variable eqFunIdx : func.
  
  Definition eqFunSig := {|
    Domain := [tTvar, tTvar];
    Range := tvProp;
    Denotation := @eq (tvarD types' tTvar)
  |}.
  Let fs' := updateAt eqFunSig fs eqFunIdx.

  Definition eqD (e1 e2 : expr types') :=
    match exprD fs' nil nil e1 tTvar, exprD fs' nil nil e2 tTvar with
      | Some v1, Some v2 => v1 = v2
      | _, _ => False
    end.

  Theorem eqD_refl : forall e1 e2, e1 = e2
    -> forall v, exprD fs' nil nil e1 tTvar = Some v
      -> eqD e1 e2.
    t.
  Qed.

  Definition eqD_seq (e1 e2 : expr types') :=
    match expr_seq_dec e1 e2 with
      | Some pf =>
        match exprD fs' nil nil e1 tTvar as v return (_ = v -> _) with
          | Some _ => fun pf' => Some (eqD_refl pf pf')
          | _ => fun _ => None
        end (refl_equal _)
      | None => None
    end.

  Fixpoint groupsOf (hyps : list (expr types')) : list (list (expr types')) :=
    match hyps with
      | nil => nil
      | h :: hyps' =>
        let grps := groupsOf hyps' in
          match h with
            | Func f [x, y] => if equiv_dec f eqFunIdx
              then addEquality eqD eqD_seq grps x y
              else grps
            | _ => grps
          end
    end.

  Definition transitivityProver (hyps : list (expr types'))
    (goal : expr types') :=
    match goal with
      | Func f [x, y] => if equiv_dec f eqFunIdx
        then inSameGroup eqD eqD_seq (groupsOf hyps) x y
        else false
      | _ => false
    end.

  Hint Resolve addEquality_sound.

  Theorem groupsOf_sound : forall hyps,
    AllProvable fs' nil nil hyps
    -> groupsEqual eqD (groupsOf hyps).
    induction hyps; repeat (apply addEquality_sound || t1).
  Qed.

  Theorem eqD_sym : forall x y, eqD x y -> eqD y x.
    t.
  Qed.

  Theorem eqD_trans : forall x y z, eqD x y -> eqD y z -> eqD x z.
    t.
  Qed.

  Theorem transitivityProverCorrect : ProverCorrect fs' transitivityProver.
    unfold transitivityProver; hnf; intros;
      match goal with
        | [ H : _ |- _ ] =>
          generalize (inSameGroup_sound eqD_sym eqD_trans eqD_seq
            (groupsOf_sound _ H)); intro Hsame
      end;
      repeat (unfold types' in *;
        match goal with
          | [ H : _ |- _ ] => apply Hsame in H
          | _ => t1
        end).
  Qed.

  Definition transitivityProverRec := {|
    prove := transitivityProver;
    prove_correct := transitivityProverCorrect
  |}.

  (* Didn't get to updating this stuff yet! *)
(*
  (* now let's use our infrastructure to prove things aren't equal *)

  Variable notFunIdx : nat.
  Hypothesis eqFun_notFun : eqFunIdx <> notFunIdx.
  Let notFunSig : signature types' := {| Domain := [tvProp]; Range := tvProp; Denotation := not |}.
  Let fs'' := updateAt notFunSig fs' notFunIdx.

  Let nth_error_fs''_notFunIdx : nth_error fs'' notFunIdx = Some notFunSig.
    provers.
  Qed.

  Hint Rewrite nth_error_updateAt_2 : provers.
  Let nth_error_fs''_eqFunIdx : nth_error fs'' eqFunIdx = Some eqFunSig.
    provers.
  Qed.

  Let eqGrouper'' := eqGrouper types natIdx fs'' eqFunIdx.
  Let enD'' := enD types natIdx fs''.

  (* tells you whether an expression is of the form "a <> b" *)
  (* makes code a lot more compact... *)
  Definition optionNeq (e : expr types') :=
    match e with
      | Func f [e'] =>
        if eq_nat_dec f notFunIdx
          then
            match e' with
              | Func g [x, y] =>
                if eq_nat_dec g eqFunIdx
                  then Some (x, y)
                  else None
              | _ => None
            end
          else None
      | _ => None
    end.

  Fixpoint notTransitivityProver (hyps : list (expr types')) (goal : expr types') :=
    match optionNeq goal with
      | Some (x, y) => let hyps' := Func eqFunIdx [x, y] :: hyps in
                       let grouped := eqGrouper'' hyps' in
                         match hyps with
                           | nil => false
                           | h :: hyps' =>
                             match optionNeq h with
                               | Some (x, y) =>
                                 if inSameGroup nat_seq_dec grouped (enD'' x) (enD'' y)
                                   then true
                                   else notTransitivityProver hyps' goal
                               | None => notTransitivityProver hyps' goal
                             end
                         end
      | None => false
    end.

  Lemma notTransitivityProver_nil : forall goal, notTransitivityProver nil goal = false.
    simpl.
    intros.
    destruct (optionNeq goal);
    [ destruct p | ];
    reflexivity.
  Qed.

  Lemma ValidProp_notFunIdx_ValidProp : forall e, ValidProp fs'' (Func notFunIdx [e]) -> ValidProp fs'' e.
    intros.
    destruct H.
    simpl in *.
    rewrite nth_error_fs''_notFunIdx in H.
    simpl in *.
    unfold ValidProp.
    destruct (exprD fs'' nil nil e tvProp).
    exists t.
    provers.
    discriminate.
  Qed.

  Hint Resolve ValidProp_notFunIdx_ValidProp.
  Lemma notFunIdx_not : forall e, ValidProp fs'' (Func notFunIdx [e]) -> exprD fs'' nil nil (Func notFunIdx [e]) tvProp = Some (~ optionDefault False (exprD fs'' nil nil e tvProp)).
    intros.
    destruct (ValidProp_notFunIdx_ValidProp H).
    provers.
  Qed.

  Hint Rewrite notFunIdx_not : provers.
  Lemma notFunIdx_eqFunIdx_neq : forall e e', ValidProp fs'' (Func notFunIdx [Func eqFunIdx [e, e']]) -> exprD fs'' nil nil (Func notFunIdx [Func eqFunIdx [e,  e']]) tvProp = Some (~ optionDefault (natTvarCoerce types natIdx 0) (exprD fs'' nil nil e natTvar) = optionDefault (natTvarCoerce types natIdx 0) (exprD fs'' nil nil e' natTvar)).
    intros.
    rewrite notFunIdx_not.
    unfold natType, types', natTvar, eqFunSig.
    provers.
    assumption.
  Qed.

  Lemma Provable_Func_neq : forall e e', Provable fs'' nil nil (Func notFunIdx [Func eqFunIdx [e, e']]) -> natTvarCoerceR types natIdx (optionDefault (natTvarCoerce types natIdx 0) (exprD fs'' nil nil e natTvar)) <> natTvarCoerceR types natIdx (optionDefault (natTvarCoerce types natIdx 0) (exprD fs'' nil nil e' natTvar)).
    unfold Provable.
    intros.
    case_eq (exprD fs'' nil nil e natTvar); case_eq (exprD fs'' nil nil e' natTvar); intros; simpl in *; hypRewriter; simpl in *.
    intro.
    apply natTvarCoerceR_inj in H2.
    rewrite H0, H1 in *.
    provers.
    provers.
    provers.
    provers.
  Qed.

  Lemma optionDefault_inj : forall A (a : A) x y, x <> None -> y <> None -> optionDefault a x = optionDefault a y -> x = y.
    intros.
    destruct x, y; simpl in *; hypRewriter; intuition.
  Qed.

  Ltac caseTac term tac := destruct term; try solve [ tac ].
  Ltac dism := simpl in *; match goal with [ H : context [ ?g ] |- ?g ] => apply H end; assumption.
  Ltac caseDismiss term := caseTac term dism.
  Hint Rewrite notTransitivityProver_nil : provers.
  Theorem notTransitivityProverCorrect : ProverCorrect fs'' notTransitivityProver.
    unfold ProverCorrect, Provable; intros.
    induction hyps.
    provers.
    unfold notTransitivityProver in H; simpl;
    fold notTransitivityProver in H.
    caseDestruct goal.
    simpl in H.
    repeat caseDestruct l.
    caseDestruct (eq_nat_dec f notFunIdx).
    caseDestruct e.
    repeat caseDestruct l.
    caseDestruct (eq_nat_dec f0 eqFunIdx).
    subst.
    simpl in H1.
    intuition.
    caseDismiss a.
    repeat caseDismiss l.
    simpl in H.
    caseDismiss (eq_nat_dec f notFunIdx).
    caseDismiss e0.
    repeat caseDismiss l.
    caseDismiss (eq_nat_dec f0 eqFunIdx).
    subst.
    autorewrite with provers in *; eauto.
    case_eq (inSameGroup nat_seq_dec
            (addEquality nat_seq_dec (eqGrouper'' hyps)
               (enD types natIdx fs'' e) (enD types natIdx fs'' e1))
            (enD'' e0) (enD'' e3)); intros; rewrite H5 in *; eauto.
    intro.
    edestruct inSameGroup_spec.
    clear H8.
    specialize (H7 H5).
    repeat destruct H7.
    eapply Provable_Func_neq; eauto.
    eauto.
    unfold enD'', enD in x.
    eauto.
    dintuition.
    eapply Provable_Func_neq; eauto.
    eapply groupsEqual_spec; eauto.
    eapply groupsEqual_addEquality; eauto.
    eapply eqGrouper_groupsEqual; eauto.
    unfold types', natType, natTvar, eqFunSig, fs', fs'' in H6.
    erewrite eqFunIdx_eq in H6; eauto.
    simpl in H6.
    apply ValidProp_notFunIdx_ValidProp in H0.
    unfold enD.
    f_equal.
    eauto.
  Qed.

  Definition notTransitivityProverRec := {| prove := notTransitivityProver; prove_correct := notTransitivityProverCorrect |}.
*)
End TransitivityProver.
