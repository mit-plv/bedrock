Require Import Inv.
Require Import Semantics.

Set Implicit Arguments.

Lemma heap_empty_bwd : Emp ===> is_heap heap_empty.
  admit.
Qed.

Definition hints_heap_empty_bwd : TacPackage.
  prepare tt heap_empty_bwd.
Defined.

