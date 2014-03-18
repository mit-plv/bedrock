Set Implicit Arguments.

Require Import Syntax.
Require Import String.
Require Import FuncCore.
Export Syntax FuncCore.

Record Func := 
  {
    Name : string;
    Core : FuncCore
  }.

Coercion Core : Func >-> FuncCore.

