Require Import AutoSep Arrays8.


Definition copyS := SPEC("dst", "dstPos", "src", "srcPos", "len") reserving 1
  Al bsD, Al bsS, Al lenD : W, Al lenS : W,
  PRE[V] array8 bsD (V "dst") * array8 bsS (V "src")
    * [| wordToNat (V "dstPos") + wordToNat (V "len") <= length bsD |]%nat
    * [| wordToNat (V "srcPos") + wordToNat (V "len") <= length bsS |]%nat
    * [| length bsD = wordToNat lenD |] * [| length bsS = wordToNat lenS |]
  POST[_] Ex bsD', array8 bsD' (V "dst") * array8 bsS (V "src")
    * [| length bsD' = length bsD |].

Definition m := bmodule "array8" {{
  bfunction "copy"("dst", "dstPos", "src", "srcPos", "len", "tmp") [copyS]
    [Al bsD, Al bsS, Al lenD : W, Al lenS : W,
      PRE[V] array8 bsD (V "dst") * array8 bsS (V "src")
        * [| wordToNat (V "dstPos") + wordToNat (V "len") <= length bsD |]%nat
        * [| wordToNat (V "srcPos") + wordToNat (V "len") <= length bsS |]%nat
        * [| length bsD = wordToNat lenD |] * [| length bsS = wordToNat lenS |]
      POST[_] Ex bsD', array8 bsD' (V "dst") * array8 bsS (V "src")
        * [| length bsD' = length bsD |] ]
    While ("len" > 0) {
      Assert [Al bsD, Al bsS, Al lenD : W, Al lenS : W,
        PRE[V] [| V "len" > natToW 0 |]%word * [| V "srcPos" < natToW (length bsS) |]%word
          * [| V "dstPos" < natToW (length bsD) |]%word
          * array8 bsD (V "dst") * array8 bsS (V "src")
          * [| wordToNat (V "dstPos") + wordToNat (V "len") <= length bsD |]%nat
          * [| wordToNat (V "srcPos") + wordToNat (V "len") <= length bsS |]%nat
          * [| length bsD = wordToNat lenD |] * [| length bsS = wordToNat lenS |]
        POST[_] Ex bsD', array8 bsD' (V "dst") * array8 bsS (V "src")
          * [| length bsD' = length bsD |] ];;

      "tmp" <-*8 "src" + "srcPos";;
      "dst" + "dstPos" *<-8 "tmp";;
      "dstPos" <- "dstPos" + 1;;
      "srcPos" <- "srcPos" + 1;;
      "len" <- "len" - 1
    };;

    Return 0
  end
}}.

Lemma rt1 : wordToNat (natToW 1) = 1.
  reflexivity.
Qed.

Hint Rewrite rt1 : N.

Lemma updown : forall (x : W) y,
  natToW 0 < x
  -> y + 1 + wordToNat (x ^- natToW 1) = y + wordToNat x.
  intros; rewrite wordToNat_wminus; nomega.
Qed.

Hint Rewrite updown using assumption : sepFormula.

Lemma natToW_wordToNat : forall w : W, natToW (wordToNat w) = w.
  apply natToWord_wordToNat.
Qed.

Hint Rewrite natToW_wordToNat : N.

Lemma goodBound : forall (x y u : W) n,
  (wordToNat x + wordToNat y <= n)%nat
  -> natToW 0 < y
  -> n = wordToNat u
  -> x < natToW n.
  intros; subst; nomega.
Qed.

Local Hint Immediate goodBound.

Theorem ok : moduleOk m.
  vcgen; abstract (sep_auto; (descend; eauto)).
Qed.
