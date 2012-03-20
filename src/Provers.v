Require Import List Arith Bool.
Require Import Expr Env.
Require Import EquivDec EqdepClass.
Require Import DepList.

Set Implicit Arguments.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Section ProverT.
  Variable types : list type.
  Variable fs : functions types.

  Definition ValidProp (e : expr types) := exists v, exprD fs nil nil e tvProp = Some v.
  Definition ValidExp (e : expr types) := exists t, exists v, exprD fs nil nil e t = Some v.

  Lemma Provable_ValidProp : forall goal, Provable fs nil nil goal
    -> ValidProp goal.
    unfold Provable, ValidProp in *; intros;
      repeat match goal with
               | [ _ : match ?E with None => _ | Some _ => _ end |- _ ] =>
                 destruct E
             end; intuition eauto.
  Qed.

  (** Provers that establish [expr]-encoded facts *)

  Definition ProverCorrect (summary : Type)
    (** Some prover work only needs to be done once per set of hypotheses,
       so we do it once and save the outcome in a summary of this type. *)
    (summarize : list (expr types) -> summary)
    (prover : summary -> expr types -> bool) :=
    forall hyps goal, prover (summarize hyps) goal = true ->
      ValidProp goal ->
      AllProvable fs nil nil hyps ->
      Provable fs nil nil goal.

  Record ProverT : Type :=
  {
    summary : Type;
    summarize : list (expr types) -> summary;
    prove : forall (hyps : summary) (goal : expr types), bool;
    prove_correct : ProverCorrect summarize prove
  }.

  (** Provers that establish equalities between [expr]-encoded terms *)

  Definition EqProverCorrect (summary : Type)
    (summarize : list (expr types) -> summary)
    (prover : summary -> expr types -> expr types -> bool) :=
    forall hyps e1 e2, prover (summarize hyps) e1 e2 = true ->
      ValidExp e1 ->
      ValidExp e2 ->
      AllProvable fs nil nil hyps ->
      exists t, match exprD fs nil nil e1 t, exprD fs nil nil e2 t with
                  | Some v1, Some v2 => v1 = v2
                  | _, _ => False
                end.

  Record EqProverT : Type :=
  {
    eq_summary : Type;
    eq_summarize : list (expr types) -> eq_summary;
    eq_prove : forall (hyps : eq_summary) (e1 e2 : expr types), bool;
    eq_prove_correct : EqProverCorrect eq_summarize eq_prove
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
                              | Equal _ _ _ => _
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
                               | Equal _ _ _ => _
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

             | [ _ : context[match ?E with (_, _) => _ end] |- _ ] => destruct E
           end.

Ltac t := repeat t1; eauto.

Section AssumptionProver.
  Variable types : list type.
  Variable fs : functions types.

  Definition assumptionSummarize (hyps : list (expr types)) := hyps.

  Fixpoint assumptionProver (hyps : list (expr types))
    (goal : expr types) : bool :=
    match hyps with
      | nil => false
      | exp :: b => if expr_seq_dec exp goal
        then true
        else assumptionProver b goal
    end.

  Theorem assumptionProverCorrect : ProverCorrect fs assumptionSummarize assumptionProver.
    t; induction hyps; t.
  Qed.

  Definition assumptionProverRec := {|
    summarize := assumptionSummarize;
    prove := assumptionProver;
    prove_correct := assumptionProverCorrect
  |}.
End AssumptionProver.

Section ReflexivityProver.
  Context {types : list type}.
  Variable fs : functions types.

  Definition reflexivitySummarize (_ : list (expr types)) := tt.

  Definition reflexivityProver (_ : unit) (goal : expr types) := 
    match goal with
      | Equal _ x y => if expr_seq_dec x y then true else false
      | _ => false
    end.

  Theorem reflexivityProverCorrect : ProverCorrect fs reflexivitySummarize reflexivityProver.
    unfold reflexivityProver; t.
  Qed.

  Definition reflexivityProverRec := {|
    summarize := reflexivitySummarize;
    prove := reflexivityProver;
    prove_correct := reflexivityProverCorrect
  |}.
End ReflexivityProver.

(* Algorithm for grouping expressions by equalities. Terribly inefficient... *)
Section Grouper.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  (* An arbitrary partial equivalence relation *)

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
      | nil => [a :: g]
      | g' :: grps' => if in_seq_dec g' a
                         then (g' ++ a :: g) :: grps'
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
    induction 1; t; eauto 7.
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
  Variable fs : functions types.

  Definition eqD (e1 e2 : expr types) : Prop :=
    match typeof fs nil nil e1 with
      | None => False
      | Some t =>
        match exprD fs nil nil e1 t, exprD fs nil nil e2 t with
          | Some v1, Some v2 => v1 = v2
          | _, _ => False
        end
    end.

  Theorem eqD_refl : forall e1 e2, e1 = e2
    -> forall t, typeof fs nil nil e1 = Some t
      -> forall v, exprD fs nil nil e1 t = Some v
        -> eqD e1 e2.
    t.
  Qed.

    Lemma nth_error_nil : forall T n,
      nth_error (@nil T) n = None.
    Proof.
      destruct n; simpl; auto.
    Qed.

  Theorem eqD_refl_wt : forall e1 e2, e1 = e2 ->
    match well_typed fs nil nil e1 return Type with
      | None => True 
      | Some t => eqD e1 e2
    end.
  Proof.
    intros; subst.
    case_eq (well_typed fs nil nil e2); intros; auto.
    generalize is_well_typed_typeof.
    generalize well_typed_is_well_typed. intros.
    generalize H. apply H0 in H.
    generalize H.
    apply is_well_typed_correct in H.
    intros.
    apply H1 in H2. destruct H.
    eapply eqD_refl; eauto.
  Qed.

  Definition eqD_seq (e1 e2 : expr types) : option (eqD e1 e2) :=
    match well_typed fs nil nil e1 as v return (_ = v -> _) with
      | None => fun _ => None
      | Some _ => fun pff => 
        match expr_seq_dec e1 e2 with
          | Some pf2 => Some 
            match pff in _ = v return match v with
                                        | None => True
                                        | Some t => eqD e1 e2
                                      end with
              | refl_equal => @eqD_refl_wt e1 e2 pf2
            end            
          | None => None
        end
    end (refl_equal _).

  Fixpoint groupsOf (hyps : list (expr types)) : list (list (expr types)) :=
    match hyps with
      | nil => nil
      | h :: hyps' =>
        let grps := groupsOf hyps' in
          match h with
            | Equal t x y => addEquality eqD eqD_seq grps x y
            | _ => grps
          end
    end.

  Definition transitivityEqProver (groups : list (list (expr types)))
    (x y : expr types) := inSameGroup eqD eqD_seq groups x y.

  Definition transitivityProver (groups : list (list (expr types)))
    (goal : expr types) :=
    match goal with
      | Equal _ x y => inSameGroup eqD eqD_seq groups x y
      | _ => false
    end.

  Hint Resolve addEquality_sound.

  Theorem exprD_principal : forall u v e t, exprD fs u v e t <> None
    -> match typeof fs u v e with
         | None => False
         | Some t' => exprD fs u v e t' <> None
       end.
    induction e; simpl; unfold lookupAs;
      repeat match goal with
               | [ |- context[nth_error ?E ?F] ] => destruct (nth_error E F) as [ [ ] | ]
               | [ H : match ?pf with refl_equal => _ end = _ |- _ ] => rewrite (UIP_refl e) in H
               | _ => t1
             end.
  Qed.

  Lemma lookupAs_det : forall v x t1 t2,
    lookupAs types v t1 x <> None
    -> lookupAs types v t2 x <> None
    -> t1 = t2.
    unfold lookupAs; t; congruence.
  Qed.

  Hint Immediate lookupAs_det.

  Theorem exprD_det : forall u v e t1 t2, exprD fs u v e t1 <> None
    -> exprD fs u v e t2 <> None
    -> t1 = t2.
    induction e; t.
  Qed.

  Ltac foundTypeof E := generalize (exprD_principal nil nil E); destruct (typeof fs nil nil E); intuition.

  Ltac foundDup E T1 T2 := match T1 with
                             | T2 => fail 1
                             | _ =>
                               assert (T1 = T2) by (apply (exprD_det nil nil E);
                                 try match goal with
                                       | [ H : _ |- _ ] => solve [ intro; apply H with T1; t ]
                                     end); subst
                           end.

  Ltac eqD1 :=
    match goal with
      | [ _ : context[typeof fs nil nil ?E] |- _ ] => foundTypeof E
      | [ |- context[typeof fs nil nil ?E] ] => foundTypeof E
      | [ _ : context[exprD fs nil nil ?E ?T1] |- context[exprD fs nil nil ?E ?T2] ] => foundDup E T1 T2
      | [ _ : context[exprD fs nil nil ?E ?T1], _ : context[exprD fs nil nil ?E ?T2] |- _ ] => foundDup E T1 T2
      | [ x : tvar, H1 : forall y : tvar, _ |- False ] => apply H1 with x; t
    end.

  Ltac eqD := unfold eqD; intros; repeat eqD1; t.
  
  Theorem eqD_sym : forall x y : expr types, eqD x y -> eqD y x.
    eqD.
  Qed.

  Theorem eqD_trans : forall x y z : expr types, eqD x y -> eqD y z -> eqD x z.
    eqD.
  Qed.

  Hint Immediate eqD_sym eqD_trans.

  Theorem groupsOf_sound : forall hyps,
    AllProvable fs nil nil hyps
    -> groupsEqual eqD (groupsOf hyps).
    induction hyps; repeat ((apply addEquality_sound; eauto; simpl in *; eqD) || t1).
  Qed.

  Theorem transitivityEqProverCorrect : EqProverCorrect fs groupsOf transitivityEqProver.
    unfold transitivityEqProver; hnf; simpl in *; intros;
      match goal with
        | [ H1 : _, H2 : _ |- _ ] =>
          apply (inSameGroup_sound eqD_sym eqD_trans eqD_seq
            (groupsOf_sound _ H1)) in H2
      end; hnf in *; simpl in *;
      generalize (exprD_principal nil nil e1); destruct (typeof fs nil nil e1);
        eauto; contradiction.
  Qed.

  Theorem transitivityProverCorrect : ProverCorrect fs groupsOf transitivityProver.
    unfold transitivityProver; hnf; intros;
      destruct goal; try discriminate;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] =>
            apply (inSameGroup_sound eqD_sym eqD_trans eqD_seq
              (groupsOf_sound _ H1)) in H2
        end; hnf in *; simpl in *; eqD.
  Qed.

  Definition transitivityProverRec := {|
    prove := transitivityProver;
    prove_correct := transitivityProverCorrect
  |}.

  Definition transitivityEqProverRec := {|
    eq_prove := transitivityEqProver;
    eq_prove_correct := transitivityEqProverCorrect
  |}.
End TransitivityProver.
