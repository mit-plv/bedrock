Require Import IL Memory String.
Require Import SyntaxExpr.

Set Implicit Arguments. 

Fixpoint exprDenote expr vs : W := 
  match expr with
    | Var str => vs str
    | Const w => w
    | Binop op a b => evalBinop op (exprDenote a vs) (exprDenote b vs)
    | TestE te a b =>  if evalTest te (exprDenote a vs) (exprDenote b vs) then $1 else $0
  end.



