Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Import SemanticsMake.
  
  Section TopSection.

    Definition heap_to_split h (_ : list (W * ArgIn)) := is_heap h.

    Lemma split_heap : forall h pairs, good_inputs h pairs -> heap_to_split h pairs ===> let h1 := make_heap pairs in is_heap h1 * is_heap (heap_diff h h1).
      admit.
    Qed.

    Definition hints_split_heap : TacPackage.
      prepare split_heap tt.
    Defined.

  End TopSection.

End Make.