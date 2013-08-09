Require Import SyntaxExpr List.

Fixpoint varsIn expr:=
  match expr with
    |Var s => s :: nil
    |Const w => nil
    |Binop op a b => varsIn a ++ varsIn b
    |TestE te a b => varsIn a ++ varsIn b
  end.

