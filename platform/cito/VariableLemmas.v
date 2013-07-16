Require Import variables Arith.
Lemma S_minus_S : forall n m, (S m <= n)%nat -> n - m = S (n - S m).
  induction n; induction m; simpl; intuition; destruct m; simpl; intuition.
Qed.
Lemma plus_n_Sn : forall n m : nat, S (n + m) = S n + m.
  induction n; induction m; simpl; intuition.
Qed.
Lemma split_tmps : forall m n, (m <= n)%nat -> tempVars n = tempVars m ++ tempChunk m (n - m) .
  Transparent tempVars tempChunk.
  induction m; induction n; unfold tempVars in *; try solve [simpl; intuition].
  intros.
  simpl.
  intuition.
  destruct (le_lt_dec (S m) n).
  erewrite IHn by eauto.
  simpl.
  rewrite app_assoc_reverse.
  f_equal.
  rewrite (@S_minus_S n m) by eauto.
  Opaque tempOf.
  simpl.
  f_equal.
  f_equal.
  f_equal.
  rewrite plus_n_Sn by eauto.
  rewrite le_plus_minus_r by eauto.
  eauto.
  replace n with m.
  rewrite minus_diag.
  simpl.
  rewrite app_assoc_reverse.
  rewrite app_nil_r.
  eauto.
  omega.
Qed.
