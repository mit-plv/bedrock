Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import ProgramLogic.
  Module Import ProgramLogicMake := Make E.

  Require Import AutoSep.
  Require Import Syntax.
  Require Import SyntaxExpr Memory IL String.
  Require Import Notations3.

  Local Open Scope expr.

  Infix ";;" := SeqEx : stmtex_scope.

  Notation "'skip'" := SkipEx : stmtex_scope.

  Notation "[ inv ] 'While' cond { body }" := (WhileEx inv cond%expr body) : stmtex_scope.

  Notation "'If' cond { trueStmt } 'else' { falseStmt }" := (IfEx cond%expr trueStmt falseStmt) : stmtex_scope.

  Notation "x <- e" := (AssignEx x e%expr) : stmtex_scope.

  Delimit Scope stmtex_scope with stmtex.

  Local Close Scope expr.

End Make.