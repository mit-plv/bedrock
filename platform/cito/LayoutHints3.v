Require Import Inv.
Require Import Semantics.

Set Implicit Arguments.

Definition is_heap_upd_option h addr a := is_heap (heap_upd_option h addr a).

Lemma is_heap_upd_option_bwd : forall h addr a, is_heap h * layout_option addr a ===> is_heap_upd_option h addr a.
  admit.
Qed.

Definition is_heap_merge h1 h2 := is_heap (heap_merge h1 h2).

Lemma is_heap_merge_bwd : forall h1 h2, is_heap h1 * is_heap h2 ===> is_heap_merge h1 h2.
  admit.
Qed.

Lemma star_merge_separated : forall specs st other h1 h2 addr adt, interp specs (![is_heap h1 * is_heap h2 * layout_option addr adt * other] st) -> separated (heap_merge h1 h2) addr adt.
  admit.
Qed.

Definition hints_heap_upd_option : TacPackage.
  prepare tt is_heap_upd_option_bwd.
Defined.

Definition hints_heap_merge : TacPackage.
  prepare tt is_heap_merge_bwd.
Defined.