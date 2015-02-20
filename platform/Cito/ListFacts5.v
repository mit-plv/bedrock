Require Import List.
Require Import Array.

Set Implicit Arguments.

Fixpoint upd_sublist big base small :=
  match small with
    | nil => big
    | x :: xs => upd_sublist (updN big base x) (1 + base) xs
  end.

Lemma length_updN : forall a b c, length (updN a b c) = length a.
  induction a; simpl; intuition.
  destruct b; simpl; auto.
Qed.

Lemma length_upd_sublist' : forall b a n, length (upd_sublist a n b) = length a.
  induction b; simpl; intuition.
  rewrite IHb.
  apply length_updN.
Qed.

Lemma length_upd_sublist : forall a n b, length (upd_sublist a n b) = length a.
  auto using length_upd_sublist'.
Qed.

Lemma map_eq_length_eq : forall A B C (f1 : A -> B) ls1 (f2 : C -> B) ls2, map f1 ls1 = map f2 ls2 -> length ls1 = length ls2.
  intros; assert (length (map f1 ls1) = length (map f2 ls2)) by congruence; repeat rewrite map_length in *; eauto.
Qed.
