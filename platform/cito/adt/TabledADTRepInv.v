Set Implicit Arguments.

Require Import TabledADT.

Section TableSection.

  Variable adt_table : ADT_Table.

  Require Import AutoSep.

  Definition RepInv ty := W -> interp_adt adt_table ty -> HProp.

  Definition RepInv_by_name s := RepInv (Primitive s).

  Require Import ilist.

  Require Import StringMapFacts.

  Definition RepInv_Table := ilist RepInv_by_name (keys adt_table).

  Variable repinv_table : RepInv_Table.

  Fixpoint interp_to_repinv (ty : ADTScheme) : RepInv ty :=
    match ty with
      | 
  
  Fixpoint interp_adt (ty : ADTScheme) : Type :=
    match ty with
      | Primitive name => 
        match find name adt_table with
          | Some type => type
          | None => Empty_set
        end
      | Product a b => (interp_adt a * interp_adt b)%type
    end.


Require Import RepInv.

Module Make1 (Import T : ADTTable).
  
  Module A := TabledADT T.

  Module Make2 <: RepInv A.

  Definition rep_inv : RepInv.

  Hypothesis rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
