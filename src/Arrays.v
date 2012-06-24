Require Import Word PropX PropXTac Memory SepIL.

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

Hint Resolve upd_length.

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
