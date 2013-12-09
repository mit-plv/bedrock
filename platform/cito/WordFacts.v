Require Import AutoSep.
Require Import Arith.

Lemma fold_4_mult : forall n, n + (n + (n + (n + 0))) = 4 * n.
  intros; ring.
Qed.

Lemma fold_4_mult_2 : 4 * 2 = 8.
  eauto.
Qed.

Lemma fold_4_mult_1 : 4 * 1 = 4.
  eauto.
Qed.

Lemma wplus_0 : forall w : W, w ^+ $0 = w.
  intros; rewrite wplus_comm; eapply wplus_unit.
Qed.

Ltac rewrite_natToW_plus :=
  repeat match goal with
           | H : context [ natToW (_ + _) ] |- _ => rewrite natToW_plus in H
           | |- context [ natToW (_ + _) ] => rewrite natToW_plus
         end.

Lemma wplus_wminus : forall (a b : W), a ^+ b ^- b = a.
  intros; words.
Qed.