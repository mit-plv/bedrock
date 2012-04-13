(** This file contains record definitions for
 ** type, function and predicate environments.
 **)
Require Import Expr SepExpr.
Require Import Env.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (SEP : SepExprType).

  Record TypeEnv (core : Repr type) (pc st : tvar) : Type :=
  { Types : Repr type
  ; Funcs : forall ts, Repr (signature (repr core (repr Types ts)))
  ; Preds : forall ts, Repr (SEP.ssignature (repr core (repr Types ts)) pc st)
  }.

End Make.
