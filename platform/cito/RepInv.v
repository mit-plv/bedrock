Set Implicit Arguments.

Require Import ADT.

Module Type RepInv (Import E : ADT).

  Require Import AutoSep.

  Definition RepInv := W -> ADTValue -> HProp.

  Parameter rep_inv : RepInv.

  Hypothesis rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.

End RepInv.
