Require Import Bedrock Heaps.


Fixpoint allWordsUpto (width init : nat) : list (word width) :=
  match init with
    | O => nil
    | S init' => natToWord width init' :: allWordsUpto width init'
  end.

Definition allWords_def (width : nat) :=
  allWordsUpto width (pow2 width).

Module Type ALL_WORDS.
  Parameter allWords : forall width : nat, list (word width).

  Axiom allWords_eq : allWords = allWords_def.
End ALL_WORDS.

Module AllWords : ALL_WORDS.
  Definition allWords := allWords_def.

  Theorem allWords_eq : allWords = allWords_def.
    reflexivity.
  Qed.
End AllWords.

Import AllWords.
Export AllWords.

Lemma natToWord_injective : forall width n n',
  (n < pow2 width)%nat
  -> (n' < pow2 width)%nat
  -> natToWord width n = natToWord width n'
  -> n = n'.
  intros.
  destruct (wordToNat_natToWord width n);
    destruct (wordToNat_natToWord width n');
      intuition.
  rewrite H1 in H4.
  rewrite H4 in H2.
  assert (x = 0).
  destruct x; simpl in *.
  omega.
  generalize dependent (x * pow2 width).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; simpl in *.
  omega.
  generalize dependent (x0 * pow2 width).
  intros.
  omega.
  subst.
  omega.
Qed.

Local Hint Constructors NoDup.

Lemma NoDup_allWordsUpto' : forall width init' init,
  init <= init' < pow2 width
  -> ~In (natToWord width init') (allWordsUpto width init).
  induction init; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] => apply natToWord_injective in H; omega
    end.
Qed.

Local Hint Resolve NoDup_allWordsUpto'.

Theorem NoDup_allWordsUpto : forall width init,
  (init <= pow2 width)%nat
  -> NoDup (allWordsUpto width init).
  induction init; simpl; intuition.
Qed.

Theorem NoDup_allWords : forall width,
  NoDup (allWords width).
  rewrite allWords_eq; intros; apply NoDup_allWordsUpto; omega.
Qed.

Module BedrockHeap.
  Definition addr := W.
  Definition byte := B.

  Definition mem := mem.

  Definition mem_get (m : mem) (a : addr) := Some (m a).

  Definition addr_dec := @weq 32.

  Definition all_addr := allWords 32.

  Theorem NoDup_all_addr : NoDup all_addr.
    apply NoDup_allWords.
  Qed.
End BedrockHeap.

Module HT := HeapTheory(BedrockHeap).
Import HT.
Export HT.
