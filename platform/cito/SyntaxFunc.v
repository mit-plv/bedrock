Require Import Syntax.
Require Import String.
Export Syntax.

Set Implicit Arguments.

Record Func := 
  {
    Name : string;
    ArgVars : list string;
    RetVar : string;
    LocalVars : list string;
    Body : Stmt
  }.

