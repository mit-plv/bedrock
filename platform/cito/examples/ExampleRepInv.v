Set Implicit Arguments.

Require Import AutoSep.
Require Import ExampleADT.
Import ExampleADT.ExampleADT.
Require Import RepInv.

Parameter is_fset : W -> WordSet.t -> HProp.

Require Import Cell SimpleCell Seq ArraySeq.

Definition rep_inv p adtvalue : HProp :=
  match adtvalue with
    | Cell v => cell v p
    | Arr ws => arr ws p
    | FSet s => is_fset p s
  end.

Module ExampleRepInv <: RepInv ExampleADT.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
    destruct a; simpl.
    eapply Himp_trans; [ apply cell_fwd | sepLemma ]; apply any_easy.
    eapply Himp_trans; [ apply arr_fwd | sepLemma ]; apply any_easy.
    admit.
  Qed.

End ExampleRepInv.
