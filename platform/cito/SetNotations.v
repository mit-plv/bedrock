Require Import SetInterface.
Require Import Equalities.

Module Notations (Key : MiniDecidableType) (Import S : Set_ Key).
  Delimit Scope set_scope with set.
  Infix "^" := mem : set_scope.
  Infix "+" := union : set_scope.
  Infix "-" := diff : set_scope.
  Notation "0" := empty : set_scope.
  Notation "!" := singleton : set_scope.
End Notations.

