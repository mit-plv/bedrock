Require Import List.
Require Import Array.

Set Implicit Arguments.

Fixpoint upd_sublist big base small :=
  match small with
    | nil => big
    | x :: xs => upd_sublist (updN big base x) (1 + base) xs
  end.

Lemma length_upd_sublist : forall a n b, length (upd_sublist a n b) = length a.
  admit.
Qed.

Lemma firstn_upd_sublist : forall a b n, n = length b -> firstn n (upd_sublist a 0 b) = b.
  admit.
Qed.

Lemma skipn_upd_sublist : forall a b n, n = length b -> skipn n (upd_sublist a 0 b) = skipn n a.
  admit.
Qed.

Lemma map_eq_length_eq : forall A B C (f1 : A -> B) ls1 (f2 : C -> B) ls2, map f1 ls1 = map f2 ls2 -> length ls1 = length ls2.
  intros; assert (length (map f1 ls1) = length (map f2 ls2)) by congruence; repeat rewrite map_length in *; eauto.
Qed.

