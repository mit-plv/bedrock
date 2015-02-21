Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import CompileFuncImpl.
  Module Import CompileFuncImplMake := Make E M.
  Import CompileFuncSpecMake.
  Require Import GoodOptimizer.
  Import GoodOptimizerMake.

  Require Import GoodFunc.

  Require Import SyntaxFunc.
  Require Import String.

  Section TopSection.

    Variable module_name : string.

    Variable func : Func.

    Hypothesis good_func : GoodFunc func.

    Variable optimizer : Optimizer.

    Hypothesis good_optimizer : GoodOptimizer optimizer.

    Definition body := body func module_name good_func good_optimizer.

    Require Import CompileFuncSpec.
    Require Import StructuredModule.
    Definition compile : function module_name :=
      (Name func, CompileFuncSpecMake.spec func, body).

  End TopSection.

End Make.