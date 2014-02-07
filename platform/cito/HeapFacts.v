Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Heap.
  Module Import HeapMake := Heap.Make E.

  Lemma heap_merge_empty : forall h, heap_merge h heap_empty = h.
    admit.
  Qed.

End Make.