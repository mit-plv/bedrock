Require Import FMapWeakList.
Require Import String.
Require Import Equalities.

Set Implicit Arguments.

Definition label := (string * string)%type.

Module Key <: MiniDecidableType.
  Definition t := label.
  Definition eq_dec (a b : label) : {a = b} + {a <> b}.
    destruct a.
    destruct b.
    destruct (string_dec s s1).
    destruct (string_dec s0 s2).
    left.
    congruence.
    right.
    congruence.
    right.
    congruence.
  Defined.
End Key.

Module Key' := Make_UDT Key.
Module LabelMap := Make Key'.


