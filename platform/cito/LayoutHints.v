Require Import Inv.
Require Import Semantics.

Set Implicit Arguments.

Module Make (Import M : RepInv.RepInv).

  Module Import InvMake := Inv.Make M.

  Section TopSection.

    Lemma heap_empty_bwd : Emp ===> is_heap heap_empty.
      admit.
    Qed.

    Definition hints_heap_empty_bwd : TacPackage.
      prepare tt heap_empty_bwd.
    Defined.

  End TopSection.

End Make.
