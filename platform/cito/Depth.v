Require Import Syntax.
Require DepthExpr.

Local Notation edepth := DepthExpr.depth.

Fixpoint depth statement :=
  match statement with
    | Syntax.Skip => 0
    | Syntax.Seq a b => max (depth a) (depth b) 
    | Syntax.If cond t f => max (edepth cond) (max (depth t) (depth f))
    | While cond body => max (edepth cond) (depth body)
    | Syntax.Call _ f args => 0 (*max (edepth f) (max (1 + edepth arg) 2)*)
  end.

