Require Import Coq.Strings.String.
Require Import Platform.Cito.SyntaxExpr.
Require Import Platform.Cito.GLabel.
Export SyntaxExpr.

Inductive Stmt : Set :=
  | Skip : Stmt
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr -> Stmt -> Stmt -> Stmt
  | While : Expr -> Stmt -> Stmt
  | Call : option string -> Expr -> list Expr -> Stmt
  | Label : string -> glabel -> Stmt
  | Assign : string -> Expr -> Stmt.