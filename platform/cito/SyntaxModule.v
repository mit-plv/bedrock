Require Import SyntaxFunc.
Require Import String.
Export SyntaxFunc.

Set Implicit Arguments.

Record Module :=
  {
    Name : string;
    Functions : list Func
  }.