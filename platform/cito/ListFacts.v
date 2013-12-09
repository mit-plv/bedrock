Require Import List.
Require Import Array.

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

