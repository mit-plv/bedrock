Require Import AutoSep.
Require Import Syntax.
Require Import SyntaxExpr Memory IL String.

Set Implicit Arguments.

Coercion Const : W >-> Expr.
Coercion Var : string >-> Expr.

Infix "+" := (Binop Plus) : expr_scope.
Infix "-" := (Binop Minus) : expr_scope.
Infix "*" := (Binop Times) : expr_scope.
Infix "=" := (TestE IL.Eq) : expr_scope.
Infix "<>" := (TestE IL.Ne) : expr_scope.
Infix "<" := (TestE IL.Lt) : expr_scope.
Infix "<=" := (TestE IL.Le) : expr_scope.

Delimit Scope expr_scope with expr.
Local Open Scope expr.

Notation "'While' ( cond ) {{ body }}" := (While cond%expr body) (no associativity, at level 55, format 
 "'[hv' 'While'  ( cond )  {{ '/  ' body '/' '}}' ']'"): stmt_scope.

Notation "'If' cond { trueStmt } 'else' { falseStmt }" := (Syntax.If cond%expr trueStmt falseStmt) : stmt_scope.

Notation "'Call' f [ arg ]" := (Syntax.Call None f arg)
  (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "x <- 'Call' f [ arg ]" := (Syntax.Call (Some x) f arg)
  (no associativity, at level 95, f at level 0) : stmt_scope.

Infix ";;" := Syntax.Seq : stmt_scope.

Notation "'skip'" := Syntax.Skip : stmt_scope.

Delimit Scope stmt_scope with stmt.
Local Open Scope stmt.
