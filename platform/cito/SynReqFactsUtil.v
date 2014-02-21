Require Import CompileStmtSpec.
Require Import StringSet.
Import StringSet.
Require Import FreeVars.
Require Import Notations.

Local Open Scope stmt.

Lemma Subset_singleton : forall x s,
  Subset (singleton x) s
  -> StringSet.In x s.
  intros.
  apply H.
  apply StringFacts.singleton_iff; auto.
Qed.

Local Hint Resolve Subset_singleton.

Lemma In_to_set' : forall x ls acc,
  In x ls \/ StringSet.In x acc
  -> StringSet.In x (fold_left (fun s e => add e s) ls acc).
  induction ls; simpl; intuition (subst; eauto).
  apply IHls.
  right; apply StringFacts.add_iff; auto.
  apply IHls.
  right; apply StringFacts.add_iff; auto.
Qed.

Lemma In_to_set : forall x ls,
  In x ls
  -> StringSet.In x (SetUtil.to_set ls).
  unfold SetUtil.to_set.
  eauto using In_to_set'.
Qed.

Local Hint Resolve In_to_set.

Lemma to_set_In' : forall x ls acc,
  StringSet.In x (fold_left (fun s e => add e s) ls acc)
  -> In x ls \/ StringSet.In x acc.
  induction ls; simpl; intuition (subst; eauto).
  apply IHls in H; intuition.
  apply StringFacts.add_iff in H0; intuition subst.
Qed.

Lemma to_set_In : forall x ls,
  StringSet.In x (SetUtil.to_set ls)
  -> In x ls.
  unfold SetUtil.to_set.
  intros.
  eapply to_set_In' in H; intuition.
  apply StringFacts.empty_iff in H0; tauto.
Qed.

Local Hint Resolve to_set_In.

Lemma Subset_union_left : forall a b c,
  Subset (StringSet.union a b) c
  -> Subset a c /\ Subset b c.
  unfold Subset; intuition;
    (apply H; apply StringFacts.union_iff; auto).
Qed.

Lemma Subset_union_right : forall a b c,
  Subset a c
  -> Subset b c
  -> Subset (StringSet.union a b) c.
  unfold Subset; intuition.
  apply StringFacts.union_iff in H1; intuition.
Qed.

Local Hint Resolve Subset_union_right Max.max_lub.
