Set Implicit Arguments.

Require Import AutoSep.
Require Import FiatADTs.
Import Adt.
Require Import Cito.RepInv.

Require Import FiniteSetF ListSetF.

Definition rep_inv p adtvalue : HProp :=
  match adtvalue with
    | List _ => [| False |]
    | Junk _ => [| False |]
    | FEnsemble s => lset s p
  end%Sep.

Module Ri <: RepInv FiatADTs.Adt.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
    destruct a; simpl.
    sepLemma.
    sepLemma.
    eapply Himp_trans; [ apply lset_fwd | sepLemma ]; apply any_easy.
  Qed.

End Ri.
