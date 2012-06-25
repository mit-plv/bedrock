Require Import Word PropX PropXTac Memory SepIL Programming.

Require Import sep.Array.

Lemma updN_length : forall ls a v,
  length (updN ls a v) = length ls.
  induction ls; simpl; intuition.
  destruct a0; simpl; auto.
Qed.

Lemma upd_length : forall ls a v,
  length (upd ls a v) = length ls.
  intros; apply updN_length.
Qed.

Hint Resolve upd_length updN_length.
Hint Rewrite upd_length updN_length : sepFormula.

Inductive containsArray : HProp -> list W -> Prop :=
| CABase : forall ls p, containsArray (array ls p) ls
| CALeft : forall P Q ls, containsArray P ls
  -> containsArray (SEP.ST.star P Q) ls
| CARight : forall P Q ls, containsArray Q ls
  -> containsArray (SEP.ST.star P Q) ls
| CAUpd : forall P ls a v, containsArray P (upd ls a v)
  -> containsArray P ls.

Hint Constructors containsArray.

Theorem containsArray_bound' : forall cs P stn ls,
  containsArray P ls
  -> forall st, interp cs (P stn st)
    -> (length ls < pow2 32)%nat.
  induction 1; intros.
  eapply array_bound; eauto.
  propxFo; eauto.
  propxFo; eauto.
  rewrite upd_length in *; eauto.
Qed.

Theorem containsArray_bound : forall cs P stn ls st,
  interp cs (![P] (stn, st))
  -> containsArray P ls
  -> (length ls < pow2 32)%nat.
  rewrite sepFormula_eq; intros; eapply containsArray_bound'; eauto.
Qed.

Hint Resolve containsArray_bound.

Require Import NArith Nomega.

Lemma bound_N_nat : forall n,
  (n < pow2 32)%nat
  -> (N.of_nat n < Npow2 32)%N.
  intros; apply Nlt_in; rewrite Npow2_nat; repeat rewrite Nat2N.id; assumption.
Qed.

Hint Resolve bound_N_nat.

Lemma sel_selN : forall ls (a : nat),
  (a < pow2 32)%nat
  -> sel ls a = selN ls a.
  unfold sel; intros; rewrite wordToNat_natToWord_idempotent; auto.
Qed.

Lemma upd_updN : forall ls (a : nat) v,
  (a < pow2 32)%nat
  -> upd ls a v = updN ls a v.
  unfold upd; intros; rewrite wordToNat_natToWord_idempotent; auto.
Qed.

Lemma pow2_pos : forall sz, (0 < pow2 sz)%nat.
  induction sz; simpl; intuition.
Qed.

Hint Immediate pow2_pos.

Hint Extern 1 (_ < _)%nat => omega.

Require Import List.

Hint Rewrite sel_selN upd_updN
  using (repeat rewrite app_length in *; solve [ eauto ]) : sepFormula.
