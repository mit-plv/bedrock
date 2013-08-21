Require Import String.
Require Import SyntaxExpr.

Inductive Statement : Set := 
  | Skip : Statement
  | Seq : Statement -> Statement -> Statement
  | If : Expr -> Statement -> Statement -> Statement
  | While : Expr -> Statement -> Statement
  | Assign : string -> Expr -> Statement
  | Call : option string -> Expr -> list Expr -> Statement.
