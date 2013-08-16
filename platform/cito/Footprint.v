Require Import Syntax List FootprintExpr.
Require Import String.

Fixpoint footprint_optional (var : option string) :=
  match var with
    | None => nil
    | Some x => x :: nil
  end.

Fixpoint footprint (statement : Statement) :=
  match statement with
    | Syntax.Skip => nil
    | Syntax.Seq a b => footprint a ++ footprint b
    | Syntax.Conditional cond t f => varsIn cond ++ footprint t ++ footprint f
    | Syntax.Loop cond body => varsIn cond ++ footprint body
    | Syntax.Assignment var val => var :: varsIn val
    | Syntax.Call var f args => footprint_optional var ++ varsIn f ++ fold_left (fun acc arg => acc ++ varsIn arg) args nil
  end.

