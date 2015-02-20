Require Import SyntaxExpr Memory IL String.

Set Implicit Arguments.

Coercion Const : W >-> Expr.
Coercion Var : string >-> Expr.

Infix "+" := (SyntaxExpr.Binop Plus) : expr_scope.
Infix "-" := (SyntaxExpr.Binop Minus) : expr_scope.
Infix "*" := (SyntaxExpr.Binop Times) : expr_scope.
Infix "=" := (SyntaxExpr.TestE IL.Eq) : expr_scope.
Infix "<>" := (SyntaxExpr.TestE IL.Ne) : expr_scope.
Infix "<" := (SyntaxExpr.TestE IL.Lt) : expr_scope.
Infix "<=" := (SyntaxExpr.TestE IL.Le) : expr_scope.

Require Import Word.

Notation "$ n" := (natToW n): expr_scope.

Delimit Scope expr_scope with expr.

