Require Import SyntaxFunc.
Require Import String.
Export SyntaxFunc.

Set Implicit Arguments.

Record CitoModule :=
  {
    ModuleName : string;
    Imports : list (string * string);
    Functions : list Func
  }.