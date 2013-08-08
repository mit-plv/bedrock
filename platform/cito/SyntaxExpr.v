Require Import IL Memory String.


Inductive Expr : Set :=
| Var : string -> Expr
| Const : W -> Expr
| Binop : binop -> Expr -> Expr -> Expr
| TestE : test -> Expr -> Expr -> Expr.

Notation "$$ x":= (Const ($ x)) (at level 0): expr_scope.
Notation "## x":= (Var x) (at level 0): expr_scope.
Infix ".+":= (Binop Plus) (at level 50): expr_scope.
Infix ".-":= (Binop Minus) (at level 50): expr_scope.
Infix ".*":= (Binop Times) (at level 50): expr_scope.
Infix ".=":= (TestE Eq) (at level 50): expr_scope.
Infix ".<>":= (TestE Ne) (at level 50): expr_scope.
Infix ".<":= (TestE Lt) (at level 50): expr_scope.
Infix ".<=":= (TestE Le) (at level 50): expr_scope.

Delimit Scope expr_scope with expr.
