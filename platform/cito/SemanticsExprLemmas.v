Require Import SyntaxExpr SemanticsExpr.
Require Import List.

Fixpoint varsIn expr:=
match expr with
  | Var s => s :: nil
  | Const w => nil
  | SyntaxExpr.Binop op a b => varsIn a ++ varsIn b
  | SyntaxExpr.TestE op a b => varsIn a ++ varsIn b
end.

