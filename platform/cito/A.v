Require Import ADT.

Module Make (E : ADT).

  Require Import Semantics.
  Module Import FMake := Make E.

End Make.