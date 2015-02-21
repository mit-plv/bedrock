Set Implicit Arguments.

Require Import Platform.Cito.ADT.
Require Import Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Platform.Cito.CompileFuncImpl.
  Module Import CompileFuncImplMake := Make E M.
  Import CompileFuncSpecMake.
  Require Import Platform.Cito.GoodOptimizer.
  Import GoodOptimizerMake.

  Require Import Platform.Cito.GoodFunc.

  Require Import Platform.Cito.SyntaxFunc.
  Require Import Coq.Strings.String.

  Section TopSection.

    Variable module_name : string.

    Variable func : Func.

    Hypothesis good_func : GoodFunc func.

    Variable optimizer : Optimizer.

    Hypothesis good_optimizer : GoodOptimizer optimizer.

    Definition body := body func module_name good_func good_optimizer.

    Require Import Platform.Cito.CompileFuncSpec.
    Require Import Bedrock.StructuredModule.
    Definition compile : function module_name :=
      (Name func, CompileFuncSpecMake.spec func, body).

  End TopSection.

End Make.