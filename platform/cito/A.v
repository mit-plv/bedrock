Require Import S.

Module Make (E : S).

  Require Import F.
  Module Import FMake := Make E.

End Make.