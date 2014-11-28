Set Implicit Arguments.

Require Import ADT RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import AutoSep.
  Require Import Inv.
  Module Import InvMake := Inv.Make E.
  Module Import InvMake2 := InvMake.Make M.
  Require Import InvFacts.
  Module Import InvFactsMake := Make E.
  Module Import InvFactsMake2 := InvFactsMake.Make M.
  Require Import LayoutHints3.
  Module Import LayoutHints3Make := Make E M.
  Require Import LayoutHints2.
  Module Import LayoutHints2Make := Make E M.
  Require Import Semantics.
  Require Import SemanticsFacts9.

  Lemma is_heap_upd_option_fwd h addr a : separated h addr a -> is_heap_upd_option h addr a ===> layout_option addr a * is_heap h.
  Proof.
    intros Hsep.
    unfold is_heap_upd_option, separated, Semantics.separated in *.
    destruct a as [a| ]; simpl in *.
    {
      destruct Hsep as [? | Hsep]; try discriminate.
      eapply Himp_trans.
      eapply Himp_trans.
      2 : eapply LayoutHints2Make.split_heap.
      {
        unfold LayoutHints2Make.heap_to_split.
        eapply Himp_refl.
      }
      {
        instantiate (1 := (addr, ADT a) :: nil).
        eapply good_inputs_add; eauto.
      }
      {
        simpl.
        Require Import SemanticsUtil.
        Import InvMake.SemanticsMake.
        unfold make_heap.
        unfold store_pair.
        unfold heap_upd.
        simpl.
        eapply Himp_star_frame.
        {
          unfold is_heap.
          unfold heap_elements.
          simpl.
          eapply Himp_trans.
          eapply Himp_star_comm.
          eapply Himp_star_Emp.
        }
        {
          eapply is_heap_Equal.
          Require Import WordMapFacts.
          eapply add_diff_singleton; eauto.
        }
      }
    }
    {
      Ltac clear_all :=
        repeat match goal with
                 | H : _ |- _ => clear H
               end.

        clear_all.
        sepLemma.
    }
  Qed.

End Make.