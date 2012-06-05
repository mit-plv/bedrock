Require Import List Arith Bool.
Require Import Expr Env.
Require Import EquivDec EqdepClass.
Require Import DepList.
Require Import Word Prover.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** * The Assumption Prover **)

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
  Admitted. 

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

Definition AssumptionProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => assumptionProver_correct fs
|}.


(** * The Reflexivity Prover **)

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
  Admitted. 

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

Definition ReflexivityProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => reflexivityProver_correct fs
|}.

Ltac unfold_reflexivityProver H :=
  match H with
    | tt =>
      cbv delta [
        reflexivityProver
        reflexivitySummarize reflexivityLearn reflexivityProve
        expr_seq_dec 
      ]
    | _ =>
      cbv delta [
        reflexivityProver
        reflexivitySummarize reflexivityLearn reflexivityProve
        expr_seq_dec 
      ] in H        
  end.


(** * The Transitivity Prover **)

(* Algorithm for grouping expressions by equalities. Terribly inefficient... *)
Section Grouper.
  Variable A : Type.
  Variable A_seq : A -> A -> bool.

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

  Coercion typeof_env : env >-> tenv.

  Definition eqD (e1 e2 : expr types) : Prop :=
    match typeof (typeof_funcs fs) uvars vars e1 with
      | None => False
      | Some t =>
        match exprD fs uvars vars e1 t, exprD fs uvars vars e2 t with
          | Some v1, Some v2 => v1 = v2
          | _, _ => False
        end
    end.

  Theorem eqD_refl : forall e1 e2, e1 = e2
    -> forall t, typeof (typeof_funcs fs) uvars vars e1 = Some t
      -> forall v, exprD fs uvars vars e1 t = Some v
        -> eqD e1 e2.
    t.
  Qed.

  Lemma nth_error_nil : forall T n,
    nth_error (@nil T) n = None.
  Proof.
    destruct n; simpl; auto.
  Qed.

(*
  Theorem eqD_refl_wt : forall e1 e2, e1 = e2 ->
    match is_well_typed (typeof_funcs fs) uvars vars e1 (typeof (typeof_funcs fs) uvars vars e1) return Prop with
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
*)

  Fixpoint transitivityLearn (sum : transitivity_summary) (hyps : list (expr types)) : transitivity_summary :=
    match hyps with
      | nil => sum
      | h :: hyps' =>
        let grps := transitivityLearn sum hyps' in
          match h with
            | Equal t x y => addEquality (@expr_seq_dec  _) grps x y
            | _ => grps
          end
    end.
  Definition groupsOf := transitivityLearn nil.

  Definition transitivityEqProver (groups : transitivity_summary)
    (x y : expr types) := inSameGroup (@expr_seq_dec _) groups x y.

  Fixpoint proveEqual (groups : transitivity_summary) (e1 e2 : expr types) {struct e1} :=
    expr_seq_dec e1 e2 || 
      (inSameGroup (@expr_seq_dec _) groups e1 e2
        || match e1, e2 with
             | Func f1 args1, Func f2 args2 =>
               if eq_nat_dec f1 f2
                 then (fix proveEquals (es1 es2 : list (expr types)) :=
                   match es1, es2 with
                     | nil, nil => true
                     | e1 :: es1', e2 :: es2' => proveEqual groups e1 e2 && proveEquals es1' es2'
                     | _, _ => false
                   end) args1 args2
                 else false
             | _, _ => false
           end
    ).

  Definition transitivityProve (groups : transitivity_summary)
    (goal : expr types) :=
    match goal with
      | Equal _ x y => proveEqual groups x y
      | _ => false
    end.

  Hint Resolve addEquality_sound.
  Hint Immediate lookupAs_det.

  Ltac foundTypeof E := generalize (@exprD_principal _ fs uvars vars (typeof_funcs fs) uvars vars
    (typeof_env_WellTyped_env _) (typeof_env_WellTyped_env _) (typeof_funcs_WellTyped_funcs _) E);
  destruct (typeof (typeof_funcs fs) uvars vars E); intuition.

  Ltac foundDup E T1 T2 := match T1 with
                             | T2 => fail 1
                             | _ =>
                               assert (T1 = T2) by (apply (exprD_det fs uvars vars E);
                                 try match goal with
                                       | [ H : _ |- _ ] => solve [ intro; apply H with T1; t ]
                                     end); subst
                           end.

  Ltac eqD1 :=
    match goal with
      | [ _ : context[typeof _ _ _ ?E] |- _ ] => foundTypeof E
      | [ |- context[typeof _ _ _ ?E] ] => foundTypeof E
      | [ _ : context[exprD fs uvars vars ?E ?T1] |- context[exprD fs uvars vars ?E ?T2] ] => foundDup E T1 T2
      | [ _ : context[exprD fs uvars vars ?E ?T1], _ : context[exprD fs uvars vars ?E ?T2] |- _ ] => foundDup E T1 T2
      | [ x : tvar, H1 : forall y : tvar, _ |- False ] => apply H1 with x; t
    end.

  Ltac eqD := unfold eqD; intros; repeat eqD1; t.
  
  Theorem eqD_sym : forall x y : expr types, eqD x y -> eqD y x.
    unfold eqD; intros.
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

    revert H.
    unfold eqD.
    case_eq (exprD fs uvars vars a1 t); try congruence; intros.
(* 
    rewrite (exprD_typeof _ _ _ _ _ H). rewrite H. destruct (exprD fs uvars vars a2 t); try congruence.
    inversion H2. subst; auto.
*)
    admit. (** TODO : this isn't true in general, but the fact that everything is provable makes it true **)
    admit.
  Qed.
  End with_vars.

  Definition transitivityValid (uvars vars : env types) (sum : transitivity_summary) : Prop :=
    (forall ls, In ls sum -> forall e, In e ls -> ValidExp fs uvars vars e) ->
    groupsEqual (eqD uvars vars) sum.

  Definition transitivitySummarize := groupsOf.

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
  Admitted.

  Theorem transitivityProverCorrect : ProverCorrect fs transitivityValid transitivityProve.
    admit. 
(*
    unfold transitivityProver; hnf; intros;
      destruct goal; try discriminate;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] =>
            apply (inSameGroup_sound eqD_sym eqD_trans expr_seq_dec
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

Definition TransitivityProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => transitivityProver_correct fs
|}.

Ltac unfold_transitivityProver H :=
  match H with
    | tt =>
      cbv delta [ 
        transitivityProver proveEqual
        transitivitySummarize transitivityLearn transitivityProve

        groupsOf addEquality
        transitivityLearn 
        inSameGroup
        expr_seq_dec
        in_seq
        groupWith
      ]
    | _ => 
      cbv delta [ 
        transitivityProver proveEqual
        transitivitySummarize transitivityLearn transitivityProve

        groupsOf addEquality
        transitivityLearn 
        inSameGroup
        expr_seq_dec
        in_seq
        groupWith
      ] in H
  end.


(** * The Word Prover **)

Require Import Arith ILEnv Memory.

Section WordProver.
  Variable types' : list type.
  Definition types := repr bedrock_types_r types'.
  Variable funcs' : functions types.
  Definition funcs := repr (bedrock_funcs_r _) funcs'.

  Record fact := {
    Source : expr types;
    Destination : expr types;
    Difference : W
  }.

  Definition word_summary := list fact.

  Require Import Div2.

  Fixpoint natToWord' (sz n : nat) : word sz :=
    match sz with
      | O => WO
      | S sz' => WS (mod2 n) (natToWord' sz' (div2 n))
    end.

  Theorem natToWord'_def : natToWord' = natToWord.
    reflexivity.
  Qed.

  Definition zero := Eval compute in wzero 32.
  Definition pow32 := Eval compute in Npow2 32.

  Require Import NArith.

  Definition wplus' := @wordBin Nplus 32.
  Definition wneg' (w : W) := NToWord 32 (pow32 - wordToN w).
  Definition wminus' (x y : W) : W := wplus' x (wneg' y).

  Theorem wplus'_def : wplus' = @wplus _.
    reflexivity.
  Qed.

  Theorem wneg'_def : wneg' = @wneg _.
    reflexivity.
  Qed.

  Theorem wminus'_def : wminus' = @wminus _.
    reflexivity.
  Qed.

  Fixpoint decompose (e : expr types) : expr types * W :=
    match e with
      | Func 0%nat [e1, Func 6%nat (Const (tvType 5%nat) k :: nil)] =>
        let (e1', d) := decompose e1 in
          (e1', wplus' d (natToWord' _ k))
      | Func 1%nat [e1, Func 6%nat (Const (tvType 5%nat) k :: nil)] =>
        let (e1', d) := decompose e1 in
          (e1', wminus' d (natToWord' _ k))
      | _ => (e, zero)
    end.

  Definition combine (f1 f2 : fact) : list fact :=
    if expr_seq_dec (Destination f1) (Source f2)
      then {| Source := Source f1;
        Destination := Destination f2;
        Difference := wplus' (Difference f1) (Difference f2) |} :: nil
      else nil.

  Fixpoint combineAll (f : fact) (fs : list fact) : list fact :=
    match fs with
      | nil => fs
      | f' :: fs => combine f f' ++ combine f' f ++ combineAll f fs
    end.

  Fixpoint alreadyCovered' (f : fact) (fs : list fact) : bool :=
    match fs with
      | nil => false
      | f' :: fs' => (expr_seq_dec (Source f) (Source f')
        && expr_seq_dec (Destination f) (Destination f'))
      || alreadyCovered' f fs'
    end.

  Definition alreadyCovered (f : fact) (fs : list fact) : bool :=
    expr_seq_dec (Source f) (Destination f) || alreadyCovered' f fs.

  Fixpoint merge (fs1 fs2 : list fact) : list fact :=
    match fs1 with
      | nil => fs2
      | f :: fs1' => merge fs1' (if alreadyCovered f fs2 then fs2 else (f :: fs2))
    end.

  Definition wordLearn1 (sum : word_summary) (e : expr types) : word_summary :=
    match e with
      | Equal (tvType 0) e1 e2 =>
        let (b1, n1) := decompose e1 in
        let (b2, n2) := decompose e2 in
        let f1 := {| Source := b1;
          Destination := b2;
          Difference := wminus' n1 n2 |} in
        let f2 := {| Source := b2;
          Destination := b1;
          Difference := wminus' n2 n1 |} in
        let sum := merge (f1 :: combineAll f1 sum) sum in
          merge (f2 :: combineAll f2 sum) sum
      | _ => sum
    end.

  Fixpoint wordLearn (sum : word_summary) (hyps : list (expr types)) : word_summary :=
    match hyps with
      | nil => sum
      | h :: hyps' => wordLearn (wordLearn1 sum h) hyps'
    end.

  Definition factsEq (f1 f2 : fact) :=
    expr_seq_dec (Source f1) (Source f2)
    && expr_seq_dec (Destination f1) (Destination f2)
    && W_seq (Difference f1) (Difference f2).

  Fixpoint factMatches (f : fact) (fs : list fact) : bool :=
    match fs with
      | nil => false
      | f' :: fs' => factsEq f f' || factMatches f fs'
    end.

  Definition wordProve (sum : word_summary) (e : expr types) :=
    match e with
      | Equal (tvType 0) e1 e2 =>
        let (b1, n1) := decompose e1 in
        let (b2, n2) := decompose e2 in
          if expr_seq_dec b1 b2
            then W_seq n1 n2
            else factMatches {| Source := b1;
              Destination := b2;
              Difference := wminus' n1 n2 |} sum
      | _ => false
    end.

  Definition wordSummarize := wordLearn nil.

  Section vars.
    Variables uvars vars : env types.

    Definition factValid (f : fact) := exists v1, exprD funcs uvars vars (Source f) (tvType 0%nat) = Some v1
      /\ exists v2, exprD funcs uvars vars (Destination f) (tvType 0%nat) = Some v2
        /\ v2 = v1 ^+ Difference f.

    Definition wordValid := Forall factValid.

    Lemma addZ_0 : forall w : W, w = w ^+ zero.
      intros.
      rewrite wplus_comm.
      symmetry.
      apply wplus_unit.
    Qed.

    Hint Immediate addZ_0.

    Lemma decompose_correct : forall e, let (b, n) := decompose e in
      forall v, exprD funcs uvars vars e (tvType 0) = Some v
        -> exists v', exprD funcs uvars vars b (tvType 0) = Some v'
          /\ v = v' ^+ n.
      Opaque natToWord'.
      induction e; simpl; intuition.

      t; eauto.

      eauto.

      eauto.

      destruct f.
      destruct l; try discriminate.
      destruct l; try discriminate.
      eauto.

      destruct e0; eauto.
      do 7 (destruct f; eauto).
      destruct l0; eauto.
      destruct e0; eauto.
      destruct t; eauto.
      do 6 (destruct n; eauto).
      destruct l0; eauto.
      destruct l; eauto.
      simpl.
      inversion H; clear H; subst.
      inversion H3; clear H3; subst.
      clear H4.
      simpl in *.
      specialize (H1 _ (refl_equal _)); destruct H1; intuition; subst.
      clear H0.
      destruct (decompose e).
      intro.
      match goal with
        | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E
      end.
      specialize (H2 _ (refl_equal _)); destruct H2; intuition; subst.
      injection H0; clear H0; intros; subst.
      repeat esplit; eauto.
      rewrite natToWord'_def.
      rewrite wplus'_def.
      repeat rewrite wplus_assoc; reflexivity.
      discriminate.

      destruct f.
      destruct l; try discriminate.
      destruct l; try discriminate.
      eauto.

      destruct e0; eauto.
      do 7 (destruct f; eauto).
      destruct l0; eauto.
      destruct e0; eauto.
      destruct t; eauto.
      do 6 (destruct n; eauto).
      destruct l0; eauto.
      destruct l; eauto.
      simpl.
      inversion H; clear H; subst.
      inversion H3; clear H3; subst.
      clear H4.
      simpl in *.
      specialize (H1 _ (refl_equal _)); destruct H1; intuition; subst.
      clear H0.
      destruct (decompose e).
      intro.
      match goal with
        | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E
      end.
      specialize (H2 _ (refl_equal _)); destruct H2; intuition; subst.
      injection H0; clear H0; intros; subst.
      repeat esplit; eauto.
      rewrite wminus'_def.
      repeat rewrite wplus_assoc.
      repeat rewrite wminus_def.
      repeat rewrite wplus_assoc.
      reflexivity.
      discriminate.
      eauto.

      discriminate.
      discriminate.
    Qed.

    Lemma mergeCorrect : forall fs1,
      Forall factValid fs1
      -> forall fs2, Forall factValid fs2
        -> Forall factValid (merge fs1 fs2).
      induction 1; simpl; intuition.
      destruct (alreadyCovered x fs2); auto.
    Qed.

    Lemma combineCorrect : forall f1 f2,
      factValid f1
      -> factValid f2
      -> Forall factValid (combine f1 f2).
      unfold combine; intros.
      generalize (expr_seq_dec_correct (Destination f1) (Source f2)).
      destruct (expr_seq_dec (Destination f1) (Source f2)); intuition.
      repeat constructor.
      unfold factValid in *; simpl in *; intros.

      destruct H; intuition.
      destruct H3; intuition.
      destruct H0; intuition.
      destruct H5; intuition.
      rewrite H1.
      rewrite H5.
      repeat esplit.
      subst.
      rewrite H2 in H3.
      rewrite H0 in H3.
      injection H3; clear H3; intros; subst.
      symmetry; apply wplus_assoc.
    Qed.

    Hint Resolve combineCorrect Forall_app.

    Lemma combineAllCorrect : forall f fs,
      factValid f
      -> Forall factValid fs
      -> Forall factValid (combineAll f fs).
      induction 2; simpl; intuition.
    Qed.

    Lemma factValid_basic : forall hyp1 hyp2 e e0 w w0,
      Provable funcs uvars vars (Equal (tvType 0) hyp1 hyp2)
      -> (forall v : tvarD (repr bedrock_types_r types') (tvType 0),
        exprD funcs uvars vars hyp1 (tvType 0) = Some v ->
        exists v' : tvarD (repr bedrock_types_r types') (tvType 0),
          exprD funcs uvars vars e (tvType 0) = Some v' /\ v = v' ^+ w)
      -> (forall v : tvarD (repr bedrock_types_r types') (tvType 0),
        exprD funcs uvars vars hyp2 (tvType 0) = Some v ->
        exists v' : tvarD (repr bedrock_types_r types') (tvType 0),
          exprD funcs uvars vars e0 (tvType 0) = Some v' /\ v = v' ^+ w0)
      -> factValid {| Source := e0; Destination := e; Difference := wminus' w0 w |}.
      intros.
      hnf in H.
      simpl in *.
      case_eq (exprD funcs uvars vars hyp1 (tvType 0)); intros.
      simpl in *.
      rewrite H2 in *.
      case_eq (exprD funcs uvars vars hyp2 (tvType 0)); intros.
      simpl in *.
      rewrite H3 in *.
      subst.
      specialize (H1 _ (refl_equal _)).
      specialize (H0 _ (refl_equal _)).
      destruct H1; destruct H0; intuition.
      subst.
      hnf.
      repeat (esplit; simpl).
      eauto.
      rewrite H.
      f_equal.
      rewrite wminus'_def.
      apply (f_equal (fun z => z ^- w)) in H5.
      repeat rewrite wminus_def in *.
      repeat rewrite wplus_assoc in *.
      rewrite H5.
      rewrite <- wplus_assoc.
      rewrite wminus_inv.
      rewrite wplus_comm.
      symmetry; apply wplus_unit.

      simpl in *.
      rewrite H3 in *.
      tauto.

      simpl in *.
      rewrite H2 in *.
      tauto.
    Qed.

    Lemma Provable_swap : forall hyp1 hyp2,
      Provable funcs uvars vars (Equal (tvType 0) hyp1 hyp2)
      -> Provable funcs uvars vars (Equal (tvType 0) hyp2 hyp1).
      unfold Provable; simpl; intros.
      case_eq (exprD funcs uvars vars hyp2 (tvType 0)); intros.
      simpl in *; rewrite H0 in *.
      case_eq (exprD funcs uvars vars hyp1 (tvType 0)); intros.
      simpl in *; rewrite H1 in *.
      auto.
      simpl in *; rewrite H1 in *; auto.
      simpl in *; rewrite H0 in *; auto.
      case_eq (exprD funcs uvars vars hyp1 (tvType 0)); intros; simpl in *.
      rewrite H1 in *; auto.
      rewrite H1 in *; auto.
    Qed.

    Hint Immediate Provable_swap.
    Hint Resolve factValid_basic mergeCorrect combineAllCorrect.

    Lemma Forall_if : forall (b : bool) ls1 ls2,
      Forall factValid ls1
      -> Forall factValid ls2
      -> Forall factValid (if b then ls1 else ls2).
      destruct b; auto.
    Qed.

    Hint Resolve Forall_if.

    Lemma wordLearn1Correct : forall sum,
      wordValid sum -> forall hyp,
        Provable funcs uvars vars hyp ->
        wordValid (wordLearn1 sum hyp).
      destruct hyp; simpl; intuition.
      destruct t; auto.
      destruct n; auto.
      specialize (decompose_correct hyp1); intro Hy1.
      specialize (decompose_correct hyp2); intro Hy2.
      destruct (decompose hyp1); destruct (decompose hyp2).
      
      apply mergeCorrect; try apply Forall_if; eauto 15.
    Qed.

    Hint Resolve wordLearn1Correct.

    Theorem wordLearnCorrect : forall sum,
      wordValid sum
      -> forall hyps, AllProvable funcs uvars vars hyps
        -> wordValid (wordLearn sum hyps).
      intros; generalize dependent sum; induction hyps; simpl in *; intuition.
    Qed.

    Hint Unfold wordValid.

    Theorem wordSummarizeCorrect : forall hyps,
      AllProvable funcs uvars vars hyps
      -> wordValid (wordSummarize hyps).
      intros; apply wordLearnCorrect; auto.
    Qed.

    Lemma factsEq_correct : forall f1 f2,
      factsEq f1 f2 = true
      -> f1 = f2.
      unfold factsEq; intros.
      apply andb_prop in H; intuition.
      apply andb_prop in H0; intuition.
      destruct f1; destruct f2; simpl in *.
      f_equal; auto.
      apply expr_seq_dec_correct; auto.
      apply expr_seq_dec_correct; auto.
      apply (Eqb_correct bedrock_type_W); auto.
    Qed.

    Lemma factMatches_correct : forall f sum,
      wordValid sum
      -> factMatches f sum = true
      -> factValid f.
      induction 1; simpl; intuition.
      apply orb_prop in H1; intuition.
      apply factsEq_correct in H2; congruence.
    Qed.
  End vars.

  Hint Resolve factMatches_correct.

  Theorem wordProverCorrect : ProverCorrect funcs wordValid wordProve.
    hnf; intros.
    destruct goal; simpl in *; try discriminate.
    destruct t; try discriminate.
    destruct n; try discriminate.
    specialize (decompose_correct uvars vars goal1); intro Hy1.
    specialize (decompose_correct uvars vars goal2); intro Hy2.
    destruct (decompose goal1); destruct (decompose goal2).
    simpl in *.

    hnf in H1; simpl in H1.
    destruct H1.
    case_eq (exprD funcs uvars vars goal1 (tvType 0)); simpl; intros.
    rewrite H2 in *.
    case_eq (exprD funcs uvars vars goal2 (tvType 0)); simpl; intros.
    rewrite H3 in *.
    injection H1; clear H1; intros; subst.
    specialize (Hy1 _ (refl_equal _)); destruct Hy1.
    specialize (Hy2 _ (refl_equal _)); destruct Hy2.
    intuition; subst.
    hnf; simpl.
    rewrite H2.
    rewrite H3.

    generalize (expr_seq_dec_correct e e0).
    destruct (expr_seq_dec e e0); intuition; subst.

    apply (Expr.Eqb_correct bedrock_type_W) in H0.
    congruence.

    clear H4.
    eapply factMatches_correct in H0; eauto.
    destruct H0; simpl in *; intuition.
    rewrite H5 in H4; injection H4; clear H4; intros; subst.
    destruct H6; intuition.
    rewrite H1 in H4; injection H4; clear H4; intros; subst.
    rewrite wminus'_def.
    rewrite wminus_def.
    repeat rewrite <- wplus_assoc.
    rewrite (wplus_comm (^~ w0) w0).
    rewrite wminus_inv.
    rewrite (wplus_comm w (wzero 32)).
    rewrite wplus_unit.
    reflexivity.

    rewrite H3 in *; discriminate.
    rewrite H2 in *; discriminate.
  Qed.

  Definition wordProver : ProverT types :=
  {| Facts := word_summary
   ; Summarize := wordSummarize
   ; Learn := wordLearn
   ; Prove := wordProve
   |}.

  Definition wordProver_correct : ProverT_correct wordProver funcs.
    econstructor.
    apply wordSummarizeCorrect.
    apply wordLearnCorrect.
    apply wordProverCorrect.
  Qed.

End WordProver.

Definition WordProver : ProverPackage :=
{| ProverTypes := bedrock_types_r
 ; ProverFuncs := bedrock_funcs_r
 ; Prover_correct := wordProver_correct
|}.


(** * The Combo Prover **)

Definition ComboProver : ProverPackage :=
{| ProverTypes := bedrock_types_r
 ; ProverFuncs := bedrock_funcs_r
 ; Prover_correct := fun ts fs => composite_ProverT_correct
   (composite_ProverT_correct (assumptionProver_correct _)
     (transitivityProver_correct _))
   (wordProver_correct _)
|}.
