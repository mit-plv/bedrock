Require Import CompileFuncImpl.
Require Import SyntaxFunc.
Require Import String.
Require Import GoodFunc GoodOptimizer.

Set Implicit Arguments.

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
    (Name func, spec func, body).

End TopSection.