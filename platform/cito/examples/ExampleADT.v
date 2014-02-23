Set Implicit Arguments.

Require Import WordMap.
Require Import OrdersAlt.

Module W_as_OT' := Update_OT W_as_OT.

Require Import MSetRBT.
Module WordSet := Make W_as_OT'.

Require Import Memory.

Inductive ADTValue :=
| FSet : WordSet.t -> ADTValue
| FMap : WordMap.t W -> ADTValue
| Cell : W -> ADTValue.

Require Import ADT.

Module ExampleADT <: ADT.

  Definition ADTValue := ADTValue.

End ExampleADT.