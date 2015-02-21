Set Implicit Arguments.

Require Import Platform.Cito.GoodModuleDec.
Require Import Platform.Cito.FuncCore.

Record CFun :=
  {
    Core : FuncCore;
    good_func : is_good_func Core = true
  }.
    
Coercion Core : CFun >-> FuncCore.

Require Import Platform.Cito.StringMap.

Record CModule := 
  {
    Funs : StringMap.t CFun
  }.
