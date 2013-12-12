Require Import Inv.
Require Import Semantics.

Set Implicit Arguments.

Definition heap_to_split h (_ : list (W * ArgIn)) := is_heap h.

Lemma split_heap : forall h pairs, good_inputs h pairs -> heap_to_split h pairs ===> let h1 := make_heap pairs in is_heap h1 * is_heap (heap_diff h h1).
  admit.
Qed.

Definition hints_split_heap : TacPackage.
  prepare split_heap tt.
Defined.

