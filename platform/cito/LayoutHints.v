Require Import Inv.
Require Import Semantics.

Set Implicit Arguments.

Lemma is_heap_upd_option_bwd : forall h addr a, is_heap h * layout_option addr a ===> is_heap (heap_upd_option h addr a).
  admit.
Qed.

Lemma star_separated : forall specs st other h addr adt, interp specs (![is_heap h * layout_option addr adt * other] st) -> separated h addr adt.
  admit.
Qed.

Lemma heap_empty_bwd : Emp ===> is_heap heap_empty.
  admit.
Qed.

Definition hints_heap_empty_bwd : TacPackage.
  prepare tt heap_empty_bwd.
Defined.

