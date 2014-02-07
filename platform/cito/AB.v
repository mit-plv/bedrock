Require Import S.

Module Make (E : S).

  Require Import A.
  Module Import AMake := Make E.
  Require Import B.
  Module Import BMake := Make E.

  Lemma foo : AMake.FMake.t = BMake.FMake.t.
    reflexivity.
  Qed.

End Make.