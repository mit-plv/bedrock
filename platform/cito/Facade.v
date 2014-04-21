Set Implicit Arguments.

Require Import String.

Require Import StringMap.
Import StringMap.

Section ADTSection.

  Variable ADT : Type.

  Inductive Ty :=
  | TInt
  | TBool 
  | TADT : Type -> Ty.

  Require Import Memory.
  Require Import IL.

  Inductive BinBoolOp := And | Or.

  Inductive Expr : Ty -> Type :=
    | ExprConstInt : W -> Expr TInt
    | ExprConstBool : bool -> Expr TBool
    | ExprConstADT : forall ADT, ADT -> Expr (TADT ADT)
    | ExprBinIntOp : Expr TInt -> binop -> Expr TInt -> Expr TInt
    | ExprBinTest : Expr TInt -> test -> Expr TInt -> Expr TBool
    | ExprBinBoolOp : Expr TBool -> BinBoolOp -> Expr TBool -> Expr TBool.

  Inductive Stmt :=
  | Skip
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr TBool -> Stmt -> Stmt -> Stmt
  | While : Expr TBool -> Stmt -> Stmt
  | Call : string -> string -> list (forall t, Expr t) -> Stmt.

  Definition State : t ADT.

  Inductive RunsTo