Require Import SyntaxFunc.
Require Import String.
Require Import LabelMap.
Require Import Semantics.
Export SyntaxFunc.

Set Implicit Arguments.

Record CitoModule :=
  {
    ModuleName : string;
    Imports : LabelMap.t Callee;
    Functions : list Func
  }.