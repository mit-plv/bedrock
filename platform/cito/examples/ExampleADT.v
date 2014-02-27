Set Implicit Arguments.

Require Import WordKey.

Require Import MSetRBT.
Module WordSet := Make W_as_OT_new.

Require Import Memory.
Require Import WordMap.

Inductive ADTValue :=
| FSet : WordSet.t -> ADTValue
| FMap : WordMap.t W -> ADTValue
| Cell : W -> ADTValue.

Require Import ADT.

Module ExampleADT <: ADT.

  Definition ADTValue := ADTValue.

End ExampleADT.