Require Import AutoSep.


Definition div4S := SPEC("n") reserving 1
  Al m,
  PRE[V] [| wordToNat (V "n") = m * 4 |]%nat
  POST[R] [| R = m |].

Definition m := bmodule "numops" {{
  bfunction "div4"("n", "acc") [div4S]
    "acc" <- 0;;

    [Al m,
      PRE[V] [| wordToNat (V "n") = m * 4 |]%nat
      POST[R] [| R = natToW m ^+ V "acc" |] ]
    While ("n" >= 4) {
      "acc" <- "acc" + 1;;
      "n" <- "n" - 4
    };;

    Return "acc"
  end
}}.

Section ok.
  Lemma use_pred : forall (w : W) n,
    wordToNat w = n * 4
    -> natToW 4 <= w
    -> wordToNat w - 4 = (pred n) * 4.
    intros.
    nomega.
  Qed.

  Hint Immediate use_pred.

  Lemma roundTrip_4 : wordToNat (natToW 4) = 4.
    auto.
  Qed.

  Hint Rewrite roundTrip_4 : N.

  Lemma cancel_pred : forall n m rv acc,
    natToW 4 <= n
    -> wordToNat n = m * 4
    -> rv = natToW (pred m) ^+ (acc ^+ natToW 1)
    -> rv = natToW m ^+ acc.
    intros; subst.
    rewrite Minus.pred_of_minus.
    rewrite natToW_minus by nomega; words.
  Qed.

  Hint Immediate cancel_pred.

  Lemma finish : forall rv acc n m,
    rv = acc
    -> n < natToW 4
    -> wordToNat n = m * 4
    -> rv = natToW m ^+ acc.
    intros; subst.
    assert (m0 = 0) by nomega.
    words.
  Qed.

  Hint Immediate finish.
  Hint Rewrite <- plus_n_O : sepFormula.

  Theorem ok : moduleOk m.
    vcgen; abstract (sep_auto; eauto).
  Qed.
End ok.
