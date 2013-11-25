Require Import SetInterface.
Require Import Equalities.

Set Implicit Arguments.

Module Relations (Key : MiniDecidableType) (Import S : Set_ Key).

  Definition subset a b := forall x, mem x a -> mem x b.
  Infix "<=" := subset : set_scope.

  Lemma subset_spec : forall a b, subset a b <-> forall x, mem x a -> mem x b.
    intuition.
  Qed.

  Lemma subset_refl : forall s, subset s s.
    unfold subset; intuition.
  Qed.

  Lemma subset_trans : forall a b c, subset a b -> subset b c -> subset a c.
    unfold subset; intuition.
  Qed.

  Lemma subset_union_left : forall a b, subset a (union a b).
    unfold subset; intros; eapply union_spec; eauto.
  Qed.
  
  Lemma subset_union_right : forall a b, subset b (union a b).
    unfold subset; intros; eapply union_spec; eauto.
  Qed.

  Lemma union_subset : forall a b c, subset a c -> subset b c -> subset (union a b) c.
    unfold subset; intros; eapply union_spec in H1; destruct H1; eauto.
  Qed.

  Lemma union_same_subset : forall s, subset (union s s) s.
    intros; eapply union_subset; eapply subset_refl.
  Qed.

  Lemma subset_union_same : forall s, subset s (union s s).
    intros; eapply subset_union_left.
  Qed.

  Lemma diff_subset : forall a b, subset (diff a b) a.
    unfold subset; intros; eapply diff_spec in H; intuition.
  Qed.

  Definition disjoint a b := forall x, mem x a -> mem x b -> False.
  Infix "*" := disjoint : set_scope.

End Relations.

Module Util (Key : MiniDecidableType) (Import S : Set_ Key).

  Lemma union_elim : forall a b x, mem x (union a b) -> mem x a \/ mem x b.
    intros; eapply union_spec in H; eauto.
  Qed.

  Lemma union_intro : forall a b x, mem x a \/ mem x b -> mem x (union a b).
    intros; eapply union_spec; eauto.
  Qed.

  Lemma mem_union_left : forall a b x, mem x a -> mem x (union a b).
    intros; eapply union_intro; intuition.
  Qed.

  Lemma mem_union_right : forall a b x, mem x b -> mem x (union a b).
    intros; eapply union_intro; intuition.
  Qed.

End Util.

Require Import Arith.

Module NatKey <: MiniDecidableType.
  Definition t := nat.
  Definition eq_dec := eq_nat_dec.
End NatKey.

Module Range (Import S : Set_ NatKey).

  Fixpoint range start length:=
    match length with
      | O => empty
      | S n' => union (range start n') (singleton (start + n'))
    end.

  Definition range0 := range 0.

End Range.