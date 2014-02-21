Require Import StringSet.
Import StringSet.

Infix "+" := union : set_scope.
Infix "<=" := Subset : set_scope.
Local Open Scope set_scope.

Ltac t := unfold Subset; intuition.

Lemma subset_refl : forall s, s <= s.
  t.
Qed.

Lemma union_subset : forall a b c, a <= c -> b <= c -> a + b <= c.
  t.
  apply StringFacts.union_iff in H1; intuition.
Qed.

Lemma subset_trans : forall a b c, a <= b -> b <= c -> a <= c.
  t.
Qed.

Lemma subset_union_left : forall a b, a <= a + b.
  t.
  apply StringFacts.union_iff; auto.
Qed.

Lemma subset_union_right : forall a b, b <= a + b.
  t.
  apply StringFacts.union_iff; auto.
Qed.

Ltac subset_solver :=
  repeat
    match goal with
      | |- ?A <= ?A => eapply subset_refl
      | |- _ + _ <= _ => eapply union_subset
      | |- ?S <= ?A + _ =>
        match A with
            context [ S ] => eapply subset_trans; [ | eapply subset_union_left]
        end
      | |- ?S <= _ + ?B =>
        match B with
            context [ S ] => eapply subset_trans; [ .. | eapply subset_union_right]
        end
    end.

Local Close Scope set_scope.