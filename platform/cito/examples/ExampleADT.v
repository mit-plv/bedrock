Set Implicit Arguments.

Require Import FiniteSet.

Import Memory.

Inductive ADTValue :=
| Cell : W -> ADTValue
| Arr : list W -> ADTValue
| FSet : WordSet.t -> ADTValue.

Require Import ADT.

Module ExampleADT <: ADT.

  Definition ADTValue := ADTValue.

End ExampleADT.