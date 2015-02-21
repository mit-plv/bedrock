Set Implicit Arguments.

Require Import Platform.Cito.ADT.
Require Import Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Platform.Cito.Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Import SemanticsMake.
  Require Import Platform.Cito.WordMap.
  Require Import Coq.FSets.FMapFacts.
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
