Require Import Syntax List FootprintExpr.

Fixpoint footprint (statement : Statement) :=
  match statement with
    | Syntax.Skip => nil
    | Syntax.Seq a b => footprint a ++ footprint b
    | Syntax.Conditional cond t f => varsIn cond ++ footprint t ++ footprint f
    | Syntax.Loop cond body => varsIn cond ++ footprint body
    | Syntax.Assignment var val => var :: varsIn val
    | Syntax.Call var f args => nil (*varsIn f ++ varsIn arg*)
    | Syntax.CallMethod var obj f args => nil                                  
  end.

