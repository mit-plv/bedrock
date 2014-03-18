Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Import SemanticsMake.
  Require Import WordMap.
  Require Import FMapFacts.
  Module Import P := Properties WordMap.

  Section TopSection.

    Lemma heap_empty_bwd : Emp ===> is_heap heap_empty.
      unfold is_heap, heap_empty, heap_elements.
      rewrite elements_empty.
      apply Himp_refl.
    Qed.

    Definition hints_heap_empty_bwd : TacPackage.
      prepare tt heap_empty_bwd.
    Defined.

  End TopSection.

End Make.
