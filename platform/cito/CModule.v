Set Implicit Arguments.

Require Import GoodModuleDec.
Require Import FuncCore.

Record CFun :=
  {
    Core : FuncCore;
    good_func : is_good_func Core = true
  }.
    
Coercion Core : CFun >-> FuncCore.

Require Import StringMap.

Record CModule := 
  {
    Funs : StringMap.t CFun
  }.
