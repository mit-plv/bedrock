Set Implicit Arguments.

Require Import Syntax.
Require Import String.

Record FuncCore := 
  {
    ArgVars : list string;
    RetVar : string;
    Body : Stmt
  }.

