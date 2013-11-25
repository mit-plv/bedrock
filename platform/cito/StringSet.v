Require Import MSetWeakList.
Require Import String.
Require Import Equalities.

Set Implicit Arguments.

Module Key <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End Key.

Module Key' := Make_UDT Key.
Module MSet := Make Key'.
Export MSet.

