Require Import String.
Require Import SyntaxExpr.

Inductive Statement : Set := 
  | Assignment : string -> Expr -> Statement
  | Skip : Statement
  | Seq : Statement -> Statement -> Statement
  | Conditional : Expr -> Statement -> Statement -> Statement
  | Loop : Expr -> Statement -> Statement
  | Call : string -> Expr -> list Expr -> Statement.
