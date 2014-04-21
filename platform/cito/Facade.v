Set Implicit Arguments.

Require Import String.

Require Import StringMap.
Import StringMap.

Section ADTSection.

  Variable ADT : Type.
  Variable ADTValue : ADT -> Type.

  Inductive Ty :=
  | TInt
  | TBool 
  | TADT : ADT -> Ty.

  Require Import Memory.
  Require Import IL.

  Inductive BinBoolOp := And | Or.

  Inductive Expr : Ty -> Type :=
    | ExprVar : forall ty, string -> Expr ty
    | ExprConstInt : W -> Expr TInt
    | ExprConstBool : bool -> Expr TBool
    | ExprConstADT : forall adt, ADTValue adt -> Expr (TADT adt)
    | ExprBinIntOp : Expr TInt -> binop -> Expr TInt -> Expr TInt
    | ExprBinTest : Expr TInt -> test -> Expr TInt -> Expr TBool
    | ExprBinBoolOp : Expr TBool -> BinBoolOp -> Expr TBool -> Expr TBool.

  Inductive Stmt :=
  | Skip
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr TBool -> Stmt -> Stmt -> Stmt
  | While : Expr TBool -> Stmt -> Stmt
  | Call : string -> string -> list (forall ty, Expr ty) -> Stmt.

  Definition State := t (forall adt, ADTValue adt).

  Fixpoint eval ty (e : Expr ty) : ty

  Inductive RunsTo : Stmt -> State -> State -> Prop :=
  | RunsToSkip : forall v, RunsTo Skip v v
  | RunsToSeq : 
      forall a b v v' v'',
        RunsTo a v v' -> 
        RunsTo b v' v'' -> 
        RunsTo (Seq a b) v v''.
  | RunsToIfTrue : 
      forall cond t f v v', 
        wneb (eval (fst v) cond) $0 = true ->
        RunsTo t v v' ->
        RunsTo (Syntax.If cond t f) v v'.
  | RunsToIfFalse : 
      forall cond t f v v', 
        wneb (eval (fst v) cond) $0 = false ->
        RunsTo f v v' ->
        RunsTo (Syntax.If cond t f) v v'
  | RunsToWhileTrue : 
      forall cond body v v' v'', 
        let loop := While cond body in
        wneb (eval (fst v) cond) $0 = true ->
        RunsTo body v v' ->
        RunsTo loop v' v'' ->
        RunsTo loop v v''
  | RunsToWhileFalse : 
      forall cond body v, 
        let loop := While cond body in
        wneb (eval (fst v) cond) $0 = false ->
        RunsTo loop v v.
