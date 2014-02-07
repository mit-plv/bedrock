Require Import ADT.

Module Make (E : ADT).

  Require Import A.
  Module AMake := Make E.
  Require Import B.
  Module BMake := Make E.

  Lemma foo : AMake.FMake.HeapMake.Heap = BMake.FMake.HeapMake.Heap.
    reflexivity.
  Qed.

End Make.