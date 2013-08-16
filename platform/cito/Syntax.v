Require Import String.
Require Import SyntaxExpr.

Inductive Statement : Set := 
  | Skip : Statement
  | Seq : Statement -> Statement -> Statement
  | Conditional : Expr -> Statement -> Statement -> Statement
  | Loop : Expr -> Statement -> Statement
  | Assignment : string -> Expr -> Statement
  | Call : option string -> Expr -> list Expr -> Statement.
