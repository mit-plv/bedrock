Require Import IL Memory String.

Inductive Expr : Set :=
| Var : string -> Expr
| Const : W -> Expr
| Binop : binop -> Expr -> Expr -> Expr
| TestE : test -> Expr -> Expr -> Expr.