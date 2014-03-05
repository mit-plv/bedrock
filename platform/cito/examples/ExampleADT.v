Set Implicit Arguments.

Require Import WordKey.

Require Import MSetRBT.
Module WordSet := Make W_as_OT_new.

Import Memory.

Inductive ADTValue :=
| Cell : W -> ADTValue
| Arr : list W -> ADTValue
| FSet : WordSet.t -> ADTValue.

Require Import ADT.

Module ExampleADT <: ADT.

  Definition ADTValue := ADTValue.

End ExampleADT.