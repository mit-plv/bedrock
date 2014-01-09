Require Import SyntaxFunc.
Require Import String.
Export SyntaxFunc.

Set Implicit Arguments.

Record CitoModule :=
  {
    ModuleName : string;
    Functions : list Func
  }.