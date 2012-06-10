Require Import List Arith Bool.
Require Import Expr Env.
Require Import EquivDec EqdepClass.
Require Import DepList.
Require Import Word Prover.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

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

    Hint Resolve combineCorrect Folds.Forall_app.

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

  Lemma wordValid_weaken : forall (u g : env types) (f : word_summary)
    (ue ge : list (sigT (tvarD types))),
    wordValid u g f -> wordValid (u ++ ue) (g ++ ge) f.
  Proof.
    unfold wordValid. induction 1; eauto.
    econstructor; eauto. clear H0 IHForall. unfold factValid in *.
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- _ ] => erewrite exprD_weaken by eauto
             | [ |- exists x, _ ] => eexists; split; [ reflexivity | ]
           end; auto.
  Qed.
  
  Definition wordProver : ProverT types :=
  {| Facts := word_summary
   ; Summarize := wordSummarize
   ; Learn := wordLearn
   ; Prove := wordProve
   |}.

  Definition wordProver_correct : ProverT_correct wordProver funcs.
    eapply Build_ProverT_correct with (Valid := wordValid);
      eauto using wordValid_weaken, wordSummarizeCorrect, wordLearnCorrect, wordProverCorrect.
  Qed.

End WordProver.

Definition WordProver : ProverPackage :=
{| ProverTypes := bedrock_types_r
 ; ProverFuncs := bedrock_funcs_r
 ; Prover_correct := wordProver_correct
|}.

