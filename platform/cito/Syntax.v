Require Import String.
Require Import SyntaxExpr.

Inductive Stmt : Set := 
  | Skip : Stmt
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr -> Stmt -> Stmt -> Stmt
  | While : Expr -> Stmt -> Stmt
  | Call : option string -> Expr -> list Expr -> Stmt.
