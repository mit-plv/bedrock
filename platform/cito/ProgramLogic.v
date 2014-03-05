Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Semantics.
  Module Import SemanticsMake := Make E.

  Definition Assert := State -> Prop.

  Require Import Syntax Notations3.

  Fixpoint wp stmt (a : Assert) : Assert :=
    match stmt with
      | x <- e => Subst a x e
      | a ;; b => wp a (wp b a)
      | If e {t} else {f} => (b /\ wp t a) \/ (~ b /\ wp f a)
      | [I] While (e) {{ body }} => I
      | DCall f ( args ) => 