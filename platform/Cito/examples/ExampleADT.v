Set Implicit Arguments.

Require Import Platform.Cito.examples.FiniteSet.

Import Memory.

Inductive ADTValue :=
| Cell : W -> ADTValue
| Arr : list W -> ADTValue
| FSet : WordSet.t -> ADTValue.

Require Import Platform.Cito.ADT.

Module ExampleADT <: ADT.

  Definition ADTValue := ADTValue.

End ExampleADT.