Require Import List.
Require Import Expr.
Require Import SepTheory PropX.

Set Implicit Arguments.

Section env.

  Variable types : list type.
  Variable funcs : functions types.

  Variable pcType : tvar types.
  Variable stateType : tvar types.

  Fixpoint spredTypeD (domain : list (tvar types)) : Type :=
    match domain with
      | nil => propX (tvarD pcType) (tvarD stateType) (map Impl types)
      | d :: domain' => tvarD d -> spredTypeD domain'
    end.
  Record ssignature := {
    SDomain : list (tvar types) ;
    SDenotation :  spredTypeD SDomain
  }.
  Variable sfuncs : list ssignature.

  Inductive sexpr : nat -> variables types -> Type :=

  | Star : forall n vars, sexpr n vars -> sexpr n vars -> sexpr n vars
  | Exists : forall n vars t, sexpr n (t :: vars)
  | Cptr : forall n vars, expr funcs vars pcType -> sexpr n vars -> sexpr n vars
  | Func : forall n vars (f : fin sfuncs), 
    hlist (expr funcs vars) (SDomain (get sfuncs f)) -> sexpr n vars
  | Const : forall n vars, 
    propX (tvarD pcType) (tvarD stateType) (map Impl types) -> sexpr n vars
    (** PtsTo should be derived, that way we can handle different sizes easily **)
  | Var0 : forall n vars, sexpr (S n) vars
  | Lift : forall n vars, sexpr n vars -> sexpr (S n) vars
  | ExistsX : forall n vars, sexpr (S n) vars -> sexpr n vars
  | ForallX : forall n vars, sexpr (S n) vars -> sexpr n vars
  .
End env.




