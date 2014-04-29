Set Implicit Arguments.

Require Import TabledADT.

Section TableSection.

  Variable adt_table : ADT_Table.

  Require Import AutoSep.

  Definition RepInv (ADTValue : Type) := W -> ADTValue -> HProp.



Require Import RepInv.

Module Make1 (Import T : ADTTable).
  
  Module A := TabledADT T.

  Module Make2 <: RepInv A.

  Definition rep_inv : RepInv.

  Hypothesis rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
