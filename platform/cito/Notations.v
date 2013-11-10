Require Import Syntax.
Import SyntaxExpr Memory IL String.

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

Notation "var <== a [ i ]" := (ReadAt var a%expr i%expr) (at level 60, a at level 0, i at level 0): stmnt_scope.
Notation "'inCase' ( cond ) {{ trueStmnt }} 'else' {{ falseStmnt }}" := (Conditional cond%expr trueStmnt falseStmnt) (no associativity, at level 55, format 
 "'[hv' 'inCase'  ( cond )  {{ '/  ' trueStmnt '/' '}}' 'else' {{ '/  ' falseStmnt '/' }} ']'"): stmnt_scope.
Notation "'While' ( cond ) {{ body }}" := (Loop cond%expr body) (no associativity, at level 55, format 
 "'[hv' 'While'  ( cond )  {{ '/  ' body '/' '}}' ']'"): stmnt_scope.

Notation "'If' cond { trueStmnt } 'Else' { falseStmnt }" := (Conditional cond%expr trueStmnt falseStmnt) (at level 55)
  : stmnt_scope.

Notation "'Call' f [ arg ]" := (Syntax.Call f arg)
  (no associativity, at level 95, f at level 0) : stmnt_scope.

Notation "a ;: b" := (Syntax.Seq a b) (at level 95, b at level 95): stmnt_scope.

Notation "var <- expr " := (Syntax.Assignment var expr%expr) (at level 90, no associativity): stmnt_scope.
Notation "var <- 'new' size" := (Syntax.Malloc var size%expr) (no associativity, at level 60): stmnt_scope.
Notation "a [ i ] <== e" := (Syntax.WriteAt a%expr i%expr e%expr) (at level 60): stmnt_scope.

Delimit Scope stmnt_scope with stmnt.
Open Scope stmnt.
