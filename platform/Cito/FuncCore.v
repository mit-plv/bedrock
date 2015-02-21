Set Implicit Arguments.

Require Import Platform.Cito.Syntax.
Require Import Coq.Strings.String.

Record FuncCore :=
  {
    ArgVars : list string;
    RetVar : string;
    Body : Stmt
  }.

