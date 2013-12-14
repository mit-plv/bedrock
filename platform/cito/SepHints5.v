Require Import SepHints2.

Set Implicit Arguments.

Lemma split_buf : forall p len pos, buf_splittable len pos -> buf_to_split p len pos ===> p =?> pos * (p ^+ $(4 * pos)) =?> (len - pos).
  admit.
Qed.

Definition hints_split_buf : TacPackage.
  prepare split_buf tt.
Defined.

