Require Import List Env.
Require Import EqdepClass.

Set Implicit Arguments.

Section env.
  Record type := {
    Impl : Type;
    Eq : forall x y : Impl, option (x = y)
  }.

  Variable types : list type.

  (** this type requires decidable equality **)
  Inductive tvar : Type :=
  | tvProp 
  | tvTrans : nat -> tvar.

  Definition tvarD (x : tvar) := 
    match x with
      | tvProp => Prop
      | tvTrans x => 
        match nth_error types x with
          | None => Empty_set
          | Some t => Impl t
        end
    end.

  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Record signature := {
    Domain : list tvar;
    Range : tvar;
    Denotation : functionTypeD (map tvarD Domain) (tvarD Range)
  }.

  Definition functions := list signature.
  Definition variables := list tvar.

  Variable funcs : functions.
  Variable uvars : variables.
  Variable vars : variables.

  Definition func := nat.
  Definition var := nat.
  Definition uvar := nat.

  Inductive expr : Type :=
  | Const : forall t : tvar, tvarD t -> expr
  | Var : forall x : var, expr
  | UVar : forall x : uvar, expr
  | Func : forall f : func, list expr -> expr.

  Global Instance EqDec_tvar : EqDec _ (@eq tvar).
   red. change (forall x y : tvar, {x = y} + {x <> y}).
    decide equality. eapply Peano_dec.eq_nat_dec.
  Defined.

  Definition env : Type := list { t : tvar & tvarD t }.

  Definition lookupAs (ls : list { t : tvar & tvarD t }) (t : tvar) (i : nat)
    : option (tvarD t) :=
    match nth_error ls i with 
      | None => None
      | Some tv => 
        match equiv_dec (projT1 tv) t with
          | left pf =>
            Some match pf in _ = t return tvarD t with
                   | refl_equal => projT2 tv
                 end
          | right _ => None
        end
    end.

  Variable uenv : list { t : tvar & tvarD t }.
  Variable env : list { t : tvar & tvarD t }.

  Section applyD.
    Variable exprD : expr -> forall t, option (tvarD t).

    Fixpoint applyD domain (xs : list expr) {struct xs}
      : forall range, functionTypeD (map tvarD domain) range -> option range :=
        match domain as domain , xs 
          return forall range, functionTypeD (map tvarD domain) range -> option range
          with
          | nil , nil => fun _ v => Some v
          | t :: ts , e :: es =>
            match exprD e t with
              | None => fun _ _ => None
              | Some v => fun r f => applyD ts es r (f v)
            end
          | _ , _ => fun _ _ => None
        end.
  End applyD.

  Fixpoint exprD (e : expr) (t : tvar) {struct e} : option (tvarD t) :=
    match e with
      | Const t' c =>
        match equiv_dec t' t with
          | left pf => 
            Some match pf in _ = t return tvarD t with 
                   | refl_equal => c
                 end
          | right _ => None 
        end
      | Var x => lookupAs env t x
      | UVar x => lookupAs uenv t x 
      | Func f xs =>
        match nth_error funcs f with
          | None => None
          | Some f =>
            match equiv_dec (Range f) t with
              | right _ => None
              | left pf => 
                match pf in _ = t return option (tvarD t) with
                  | refl_equal =>
                    applyD (exprD) _ xs _ (Denotation f)
                end
            end
        end
    end.

  Fixpoint liftExpr (a b : nat) (e : expr) {struct e} : expr :=
    match e with
      | Const t' c => Const t' c
      | Var x => 
        if Compare_dec.lt_dec a x
        then Var x
        else Var (x + b)          
      | UVar x => UVar x
      | Func f xs => 
        Func f (map (liftExpr a b) xs)
    end.

End env.