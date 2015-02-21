Set Implicit Arguments.

Require Import Platform.Cito.Syntax.
Require Import Coq.Strings.String.
Require Import Platform.Cito.FuncCore.
Export Syntax FuncCore.

Record Func :=
  {
    Name : string;
    Core : FuncCore
  }.

Coercion Core : Func >-> FuncCore.

