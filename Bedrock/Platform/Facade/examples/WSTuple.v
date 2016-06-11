Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Arrays8.
Require Import Bedrock.Platform.Facade.examples.ByteString.


Module Type ADT.
  Parameter wstuple : WSTupl -> W -> HProp.
  Parameter wstuple' : WSTupl -> W -> HProp.

  Axiom wstuple_fwd : forall ws p, wstuple ws p ===> wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |].
  Axiom wstuple_bwd : forall ws p, wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |] ===> wstuple ws p.

  Axiom wstuple'_nil_fwd : forall p, wstuple' nil p ===> Emp.
  Axiom wstuple'_word_fwd : forall w ws' p, wstuple' (WSWord w :: ws') p ===> (p ==*> $0, w) * wstuple' ws' (p ^+ $8).
  Axiom wstuple'_bytes_fwd : forall capacity bs ws' p, wstuple' (WSBytes capacity bs :: ws') p ===> Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8).

  Axiom wstuple'_nil_bwd : forall p, Emp ===> wstuple' nil p.
  Axiom wstuple'_word_bwd : forall w ws' p, (p ==*> $0, w) * wstuple' ws' (p ^+ $8) ===> wstuple' (WSWord w :: ws') p.
  Axiom wstuple'_bytes_bwd : forall capacity bs ws' p, Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8) ===> wstuple' (WSBytes capacity bs :: ws') p.
End ADT.

Module Import Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint wstuple' (ws : WSTupl) (p : W) : HProp :=
    match ws with
    | nil => Emp
    | WSWord w :: ws' => (p ==*> $0, w) * wstuple' ws' (p ^+ $8)
    | WSBytes capacity bs :: ws' => Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8)
    end.

  Definition wstuple (ws : WSTupl) (p : W) : HProp :=
    wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |].

  Theorem wstuple_fwd : forall ws p, wstuple ws p ===> wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |].
  Proof.
    unfold wstuple; sepLemma.
  Qed.

  Theorem wstuple_bwd : forall ws p, wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |] ===> wstuple ws p.
  Proof.
    unfold wstuple; sepLemma.
  Qed.

  Theorem wstuple'_nil_fwd : forall p, wstuple' nil p ===> Emp.
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_word_fwd : forall w ws' p, wstuple' (WSWord w :: ws') p ===> (p ==*> $0, w) * wstuple' ws' (p ^+ $8).
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_bytes_fwd : forall capacity bs ws' p, wstuple' (WSBytes capacity bs :: ws') p ===> Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8).
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_nil_bwd : forall p, Emp ===> wstuple' nil p.
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_word_bwd : forall w ws' p, (p ==*> $0, w) * wstuple' ws' (p ^+ $8) ===> wstuple' (WSWord w :: ws') p.
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_bytes_bwd : forall capacity bs ws' p, Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8) ===> wstuple' (WSBytes capacity bs :: ws') p.
  Proof.
    sepLemma.
  Qed.
End Adt.

Export Adt.

Lemma expose_words : forall p len : W,
    len <> $0
    -> p =?> (wordToNat len * 2)
         ===> Ex w1, Ex w2, (p ==*> w1, w2) * (p ^+ $8) =?> (wordToNat (len ^- $1) * 2).
Proof.
  intros.
  case_eq (wordToNat len); intros.

  apply (f_equal (natToWord 32)) in H0.
  rewrite natToWord_wordToNat in H0.
  tauto.

  sepLemma.
  apply allocated_shift_base.
  words.
  rewrite wordToNat_wminus; auto.
  pre_nomega.
  change (wordToNat (natToW 1)) with 1.
  omega.
Qed.

Fixpoint zeroes (n : nat) : WSTupl :=
  match n with
  | O => nil
  | S n' => WSWord 0 :: zeroes n'
  end.

Lemma zeroes_nonzero_bwd : forall w p : W,
    w <> $0
    -> (p ==*> $0, $0) * wstuple' (zeroes (wordToNat (w ^- $1))) (p ^+ $8)
       ===> wstuple' (zeroes (wordToNat w)) p.
Proof.
  intros.
  rewrite wordToNat_wminus.
  change (wordToNat $1) with 1.
  case_eq (wordToNat w); intros.
  apply (f_equal (natToWord 32)) in H0.
  rewrite natToWord_wordToNat in H0.
  tauto.
  simpl.
  replace (n - 0) with n by omega.
  eapply Himp_trans; [ | apply wstuple'_word_bwd ].
  sepLemma.
  pre_nomega.
  change (wordToNat ($1)) with 1.
  case_eq (wordToNat w); intros.
  apply (f_equal (natToWord 32)) in H0.
  rewrite natToWord_wordToNat in H0.
  tauto.
  omega.
Qed.

Definition hints : TacPackage.
  prepare (wstuple_fwd, wstuple'_nil_fwd, wstuple'_word_fwd, wstuple'_bytes_fwd,
           expose_words)
          (wstuple_bwd, wstuple'_nil_bwd, wstuple'_word_bwd, wstuple'_bytes_bwd,
           zeroes_nonzero_bwd).
Defined.

Definition newS := SPEC("extra_stack", "len") reserving 8
  PRE[V] [| wordToNat (V "len") >= 1 |]%nat * [| goodSize (wordToNat (V "len") * 2) |] * mallocHeap 0
  POST[R] wstuple (zeroes (wordToNat (V "len"))) R * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "WSTuple" {{
    bfunction "new"("extra_stack", "len", "tmp") [newS]
      "extra_stack" <- "len" * 2;;
      "extra_stack" <-- Call "malloc"!"malloc"(0, "extra_stack")
      [PRE[V, R] R =?> (wordToNat (V "len") * 2) * [| goodSize (wordToNat (V "len") * 2) |]
       POST[R'] [| R' = R |] * wstuple' (zeroes (wordToNat (V "len"))) R];;

      "tmp" <- "extra_stack";;
      [PRE[V] V "tmp" =?> (wordToNat (V "len") * 2) * [| goodSize (wordToNat (V "len") * 2) |]
       POST[R] [| R = V "extra_stack" |] * wstuple' (zeroes (wordToNat (V "len"))) (V "tmp")]
      While ("len" <> 0) {
        "tmp" *<- 0;;
        "tmp"+4 *<- 0;;
        "tmp" <- "tmp" + 8;;
        "len" <- "len" - 1
      };;

      Return "extra_stack"
    end
  }}.

Lemma two_le : forall w : W,
    (wordToNat w >= 1)%nat
    -> goodSize (wordToNat w * 2)
    -> $2 <= w ^* $2.
Proof.
  intros.
  pre_nomega.
  rewrite wordToNat_wmult.
  change (wordToNat $2) with 2.
  omega.
  assumption.
Qed.

Hint Immediate two_le.

Lemma times2 : forall w : W,
    goodSize (wordToNat w * 2)
    -> wordToNat (w ^* $2) = wordToNat w * 2.
Proof.
  intros; pre_nomega.
  rewrite wordToNat_wmult; auto.
Qed.

Hint Rewrite times2 using assumption : sepFormula.

Lemma length_zeroes : forall n,
    length (zeroes n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Hint Rewrite length_zeroes : sepFormula.

Lemma goodSize_minus1 : forall w : W,
    goodSize (wordToNat w * 2)
    -> w <> $0
    -> goodSize (wordToNat (w ^- $1) * 2).
Proof.
  intros.
  eapply goodSize_weaken; eauto.
  rewrite wordToNat_wminus.
  change (wordToNat ($1)) with 1.
  omega.
  pre_nomega.
  case_eq (wordToNat w); intros.
  apply (f_equal (natToWord 32)) in H1.
  rewrite natToWord_wordToNat in H1.
  tauto.
  change (wordToNat ($1)) with 1.
  omega.
Qed.

Hint Immediate goodSize_minus1.

Lemma zeroes_zero_bwd : forall w p : W,
    w = $0
    -> p =?> (wordToNat w * 2) ===> wstuple' (zeroes (wordToNat w)) p.
Proof.
  intros; subst.
  change (wordToNat $0) with 0.
  simpl.
  apply wstuple'_nil_bwd.
Qed.

Hint Extern 1 (himp _ _ _) => apply zeroes_zero_bwd.

Ltac t := sep hints; auto.

Local Hint Extern 1 (@eq W _ _) => words.
Local Hint Extern 1 (freeable _ _) => congruence.

Theorem ok : moduleOk m.
Proof.
  vcgen.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
Qed.
