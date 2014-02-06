Require Import AutoSep.
Require Import Semantics.

Set Implicit Arguments.

Module Type RepInv.

  Definition RepInv := W -> ADTValue -> HProp.

  Parameter rep_inv : RepInv.

  Hypothesis rep_inv_ptr : forall p a spec st, interp spec (![rep_inv p a] st) -> exists other, interp spec (![p =?> 1 * other] st).

End RepInv.