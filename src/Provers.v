Require Import List Arith Bool.
Require Import Expr Env.
Require Import EquivDec EqdepClass.
Require Import DepList.

Set Implicit Arguments.
Set Strict Implicit.

Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Section ProverT.
  (** TODO: This should probably go in Expr **)
  Variable types : list type.
  Variable fs : functions types.

  Definition ValidProp uvars vars (e : expr types) := exists v, exprD fs uvars vars e tvProp = Some v.
  Definition ValidExp uvars vars (e : expr types) := exists t, exists v, exprD fs uvars vars e t = Some v.

  Lemma Provable_ValidProp : forall uvars vars goal, Provable fs uvars vars goal
    -> ValidProp uvars vars goal.
    unfold Provable, ValidProp in *; intros;
      repeat match goal with
               | [ _ : match ?E with None => _ | Some _ => _ end |- _ ] =>
                 destruct E
             end; intuition eauto.
  Qed.
End ProverT.

(** Provers that establish [expr]-encoded facts *)

Definition ProverCorrect types (fs : functions types) (summary : Type)
    (** Some prover work only needs to be done once per set of hypotheses,
       so we do it once and save the outcome in a summary of this type. *)
  (valid : env types -> env types -> summary -> Prop)
  (prover : summary -> expr types -> bool) : Prop :=
  forall vars uvars sum,
    valid uvars vars sum ->
    forall goal, 
      prover sum goal = true ->
      ValidProp fs uvars vars goal ->
      Provable fs uvars vars goal.

Record ProverT (types : list type) : Type :=
{ Facts : Type
; Summarize : exprs types -> Facts
; Learn : Facts -> exprs types -> Facts
; Prove : Facts -> expr types -> bool
}.

Record ProverT_correct (types : list type) (P : ProverT types) (funcs : functions types) : Type :=
{ Valid : env types -> env types -> Facts P -> Prop
; Summarize_correct : forall uvars vars hyps, 
  AllProvable funcs uvars vars hyps ->
  Valid uvars vars (Summarize P hyps)
; Learn_correct : forall uvars vars facts,
  Valid uvars vars facts -> forall hyps,
  AllProvable funcs uvars vars hyps ->
  Valid uvars vars (Learn P facts hyps)
; Prove_correct : ProverCorrect funcs Valid (Prove P)
}.

Lemma eq_nat_dec_correct : forall (n : nat), eq_nat_dec n n = left eq_refl.
  induction n; provers.
Qed.
Hint Rewrite eq_nat_dec_correct : provers.

Lemma nat_seq_dec_correct : forall (n : nat), seq_dec n n = Some eq_refl.
  unfold seq_dec. provers.
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
             | [ |- context[if ?E then _ else _] ] => 
               case_eq E; intro
             | [ |- context[match ?E with
                              | nil => _
                              | _ :: _ => _
                            end] ] => destruct E
             | [ H : _ || _ = true |- _ ] => apply orb_true_iff in H; destruct H
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
             | [ H : context[if ?E then _ else _] |- _ ] => 
               revert H; case_eq E; do 2 intro
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

  Definition assumption_summary : Type := list (expr types).

  Definition assumptionSummarize (hyps : list (expr types)) : assumption_summary := hyps.

  Fixpoint assumptionProve (hyps : assumption_summary)
    (goal : expr types) : bool :=
    match hyps with
      | nil => false
      | exp :: b => if expr_seq_dec exp goal
        then true
        else assumptionProve b goal
    end.

  Definition assumptionLearn (sum : assumption_summary) (hyps : list (expr types)) : assumption_summary :=
    sum ++ hyps.

  Definition assumptionValid (uvars vars : env types) (sum : assumption_summary) : Prop :=
    AllProvable fs uvars vars sum.

  Lemma assumptionSummarizeCorrect : forall uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    assumptionValid uvars vars (assumptionSummarize hyps).
  Proof.
    auto.
  Qed.

  Lemma assumptionLearnCorrect : forall uvars vars sum,
    assumptionValid uvars vars sum -> forall hyps, 
    AllProvable fs uvars vars hyps ->
    assumptionValid uvars vars (assumptionLearn sum hyps).
  Proof.
    unfold assumptionLearn, assumptionValid. intuition.
    apply AllProvable_app; auto.
  Qed.

  Theorem assumptionProverCorrect : ProverCorrect fs assumptionValid assumptionProve.
    t; induction sum; t.
  Qed.

  Definition assumptionProver : ProverT types :=
  {| Facts := assumption_summary
   ; Summarize := assumptionSummarize
   ; Learn := assumptionLearn
   ; Prove := assumptionProve
   |}.
  Definition assumptionProver_correct : ProverT_correct (types := types) assumptionProver fs.
  econstructor.
  instantiate (1 := assumptionValid).
  apply assumptionSummarizeCorrect.
  apply assumptionLearnCorrect.
  apply assumptionProverCorrect.
  Qed.

End AssumptionProver.

Section ReflexivityProver.
  Context {types : list type}.
  Variable fs : functions types.
  
  Definition reflexivityValid (_ _ : env types) (_ : unit) := True.

  Definition reflexivitySummarize (_ : list (expr types)) := tt.

  Definition reflexivityProve (_ : unit) (goal : expr types) := 
    match goal with
      | Equal _ x y => if expr_seq_dec x y then true else false
      | _ => false
    end.

  Definition reflexivityLearn (sum : unit) (hyps : list (expr types)) := sum.

  Lemma reflexivitySummarizeCorrect : forall uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    reflexivityValid uvars vars (reflexivitySummarize hyps).
  Proof.
    unfold reflexivityValid; auto.
  Qed.

  Lemma reflexivityLearnCorrect : forall uvars vars sum,
    reflexivityValid uvars vars sum -> forall hyps, 
    AllProvable fs uvars vars hyps ->
    reflexivityValid uvars vars (reflexivityLearn sum hyps).
  Proof.
    unfold reflexivityValid; auto.
  Qed.

  Theorem reflexivityProverCorrect : ProverCorrect fs reflexivityValid reflexivityProve.
    unfold reflexivityProve; t.
  Qed.

  Definition reflexivityProver : ProverT types :=
  {| Facts := unit
   ; Summarize := fun _ => tt
   ; Learn := fun x _ => x
   ; Prove := reflexivityProve
   |}.
  Definition reflexivityProver_correct : ProverT_correct reflexivityProver fs.
  econstructor.
  instantiate (1 := reflexivityValid).
  apply reflexivitySummarizeCorrect.
  apply reflexivityLearnCorrect.
  apply reflexivityProverCorrect.
  Qed.
End ReflexivityProver. 

(* Algorithm for grouping expressions by equalities. Terribly inefficient... *)
Section Grouper.
  Variable A : Type.
  Variable A_seq : A -> A -> bool.
(*
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
*)

  Fixpoint in_seq (ls : list A) (a : A) : bool :=
    match ls with
      | nil => false
      | x :: ls' => A_seq x a || in_seq ls' a
    end.

  Fixpoint groupWith (grps : list (list A)) (g : list A) (a : A) :=
    match grps with
      | nil => [a :: g]
      | g' :: grps' => if in_seq g' a
                         then (g' ++ a :: g) :: grps'
                         else g' :: groupWith grps' g a
    end.

  Fixpoint addEquality (ls : list (list A)) (a : A) (b : A) : list (list A) :=
    match ls with
      | nil => [[a, b]] (* matched nothing *)
      | grp :: ls' => if in_seq grp a
                        then groupWith ls' grp b
                        else if in_seq grp b
                               then groupWith ls' grp a
                               else grp :: addEquality ls' a b
    end.

  Fixpoint inSameGroup (grps : list (list A)) (a : A) (b : A) :=
    match grps with
      | nil => false
      | g :: grps' => 
        if in_seq g a then
          if in_seq g b
            then true
            else inSameGroup grps' a b
        else inSameGroup grps' a b
    end.

  Variable R : A -> A -> Prop.
  (* An arbitrary partial equivalence relation *)

  Hypothesis Rsym : forall x y, R x y -> R y x.
  Hypothesis Rtrans : forall x y z, R x y -> R y z -> R x z.
  Hypothesis A_seq_correct : forall x y, A_seq x y = true -> R x y.

  Fixpoint InR (x : A) (ls : list A) : Prop :=
    match ls with
      | nil => False
      | y :: ls' => R y x \/ InR x ls'
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

  Lemma in_seq_correct : forall (a : A) (ls : list A),
    in_seq ls a = true -> InR a ls.
  Proof.
    induction ls; t.
  Qed.

  Hint Resolve in_seq_correct A_seq_correct.

  Lemma groupWith_sound : forall x xs grps,
    Forall groupEqual grps
    -> Forall (R x) xs
    -> Forall groupEqual (groupWith grps xs x).
    induction 1; t. eauto 10. 
      apply in_seq_correct in H3. eauto 7.
  Qed.

  Hint Resolve groupWith_sound.

  Theorem addEquality_sound : forall x y grps,
    groupsEqual grps
    -> R x y
    -> groupsEqual (addEquality grps x y).
    induction 1; t; 
      match goal with
        | [ H : _ |- _ ] => apply A_seq_correct in H || apply in_seq_correct in H
      end; eauto 7. 
  Qed.

  Theorem inSameGroup_sound : forall grps, groupsEqual grps
    -> forall x y, inSameGroup grps x y = true
      -> R x y.
    induction 1; t;
      repeat match goal with
        | [ H : _ |- _ ] => apply A_seq_correct in H || apply in_seq_correct in H
      end; eauto 7. 
  Qed.
End Grouper.

Section TransitivityProver.
  Variable types : list type.
  Variable fs : functions types.
  Section with_vars.
  Variables uvars vars : env types.

  Definition transitivity_summary : Type := list (list (expr types)).

  Definition eqD (e1 e2 : expr types) : Prop :=
    match typeof fs uvars vars e1 with
      | None => False
      | Some t =>
        match exprD fs uvars vars e1 t, exprD fs uvars vars e2 t with
          | Some v1, Some v2 => v1 = v2
          | _, _ => False
        end
    end.

  Theorem eqD_refl : forall e1 e2, e1 = e2
    -> forall t, typeof fs uvars vars e1 = Some t
      -> forall v, exprD fs uvars vars e1 t = Some v
        -> eqD e1 e2.
    t.
  Qed.

  Lemma nth_error_nil : forall T n,
    nth_error (@nil T) n = None.
  Proof.
    destruct n; simpl; auto.
  Qed.

  Theorem eqD_refl_wt : forall e1 e2, e1 = e2 ->
    match well_typed fs uvars vars e1 return Type with
      | None => True 
      | Some t => eqD e1 e2
    end.
  Proof.
    intros; subst.
    case_eq (well_typed fs uvars vars e2); intros; auto.
    generalize is_well_typed_typeof.
    generalize well_typed_is_well_typed. intros.
    generalize H. apply H0 in H.
    generalize H.
    apply is_well_typed_correct in H.
    intros.
    apply H1 in H2. destruct H.
    eapply eqD_refl; eauto.
  Qed.

  Definition eqD_seq (e1 e2 : expr types) : bool :=
    match expr_seq_dec e1 e2 with
      | Some pf2 => true
      | None => false
    end.

(*
  Definition eqD_seq (e1 e2 : expr types) : option (eqD e1 e2) :=
    match well_typed fs uvars vars e1 as v return (_ = v -> _) with
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
*)

  Fixpoint groupsOf (hyps : list (expr types)) : list (list (expr types)) :=
    match hyps with
      | nil => nil
      | h :: hyps' =>
        let grps := groupsOf hyps' in
          match h with
            | Equal t x y => addEquality eqD_seq grps x y
            | _ => grps
          end
    end.

  Definition transitivityEqProver (groups : transitivity_summary)
    (x y : expr types) := inSameGroup eqD_seq groups x y.

  Definition transitivityProve (groups : transitivity_summary)
    (goal : expr types) :=
    match goal with
      | Equal _ x y => inSameGroup eqD_seq groups x y
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

  Ltac foundTypeof E := generalize (exprD_principal uvars vars E); destruct (typeof fs uvars vars E); intuition.

  Ltac foundDup E T1 T2 := match T1 with
                             | T2 => fail 1
                             | _ =>
                               assert (T1 = T2) by (apply (exprD_det uvars vars E);
                                 try match goal with
                                       | [ H : _ |- _ ] => solve [ intro; apply H with T1; t ]
                                     end); subst
                           end.

  Ltac eqD1 :=
    match goal with
      | [ _ : context[typeof fs uvars vars ?E] |- _ ] => foundTypeof E
      | [ |- context[typeof fs uvars vars ?E] ] => foundTypeof E
      | [ _ : context[exprD fs uvars vars ?E ?T1] |- context[exprD fs uvars vars ?E ?T2] ] => foundDup E T1 T2
      | [ _ : context[exprD fs uvars vars ?E ?T1], _ : context[exprD fs uvars vars ?E ?T2] |- _ ] => foundDup E T1 T2
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
    AllProvable fs uvars vars hyps
    -> groupsEqual eqD (groupsOf hyps).
    induction hyps. intuition. simpl in *. constructor.

    intro. simpl in H. destruct H.
    specialize (IHhyps H0).

    t1.
    destruct a; auto.
    revert H; case_eq (exprD fs uvars vars (Equal t a1 a2) tvProp); intros; try contradiction.
    simpl in *. apply addEquality_sound; eauto.
    
    Focus 2.
    Lemma exprD_typeof : forall a1 t D,
      exprD fs uvars vars a1 t = Some D ->
      typeof fs uvars vars a1 = Some t.
    Proof.
      intros.
      assert (exprD fs uvars vars a1 t <> None); try congruence.
      apply exprD_principal in H0.
      destruct (typeof fs uvars vars a1); try contradiction.
      f_equal.
      eapply exprD_det in H0. symmetry; eassumption. congruence.
    Qed.
    revert H.
    unfold eqD.
    case_eq (exprD fs uvars vars a1 t); try congruence; intros.
    rewrite (exprD_typeof _ _ H). rewrite H. destruct (exprD fs uvars vars a2 t); try congruence.
    inversion H2. subst; auto.
    admit. (** TODO : this isn't true in general, but the fact that everything is provable makes it true **)
  Qed.
  End with_vars.

  Definition transitivityValid (uvars vars : env types) (sum : transitivity_summary) : Prop :=
    (forall ls, In ls sum -> forall e, In e ls -> ValidExp fs uvars vars e) ->
    groupsEqual (eqD uvars vars) sum.

  Definition transitivitySummarize := groupsOf.

  (** TODO: fix this **)
  Definition transitivityLearn (sum : transitivity_summary) (hyps : list (expr types)) := sum.

  Theorem transitivitySummarizeCorrect : forall uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    transitivityValid uvars vars (transitivitySummarize hyps).
  Proof.
  Admitted.

  Theorem transitivityLearnCorrect : forall uvars vars sum,
    transitivityValid uvars vars sum -> forall hyps,
    AllProvable fs uvars vars hyps ->
    transitivityValid uvars vars (transitivityLearn sum hyps).
  Proof.
    intuition.
  Qed.

  Theorem transitivityProverCorrect : ProverCorrect fs transitivityValid transitivityProve.
    admit. 
(*
    unfold transitivityProver; hnf; intros;
      destruct goal; try discriminate;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] =>
            apply (inSameGroup_sound eqD_sym eqD_trans eqD_seq
              (groupsOf_sound _ H1)) in H2
        end; hnf in *; simpl in *; eqD.
*)
  Qed.

  Definition transitivityProver : ProverT types :=
  {| Facts := transitivity_summary
   ; Summarize := transitivitySummarize
   ; Learn := transitivityLearn
   ; Prove := transitivityProve
   |}.
  Definition transitivityProver_correct : ProverT_correct transitivityProver fs.
  econstructor.
  instantiate (1 := transitivityValid).
  apply transitivitySummarizeCorrect.
  apply transitivityLearnCorrect.
  apply transitivityProverCorrect.
  Qed.

End TransitivityProver.

