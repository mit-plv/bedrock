Require Import List Env.
Require Import EqdepClass.

Set Implicit Arguments.

Section env.
  Record type := Typ {
    Impl : Type;
    Eq : forall x y : Impl, option (x = y)
  }.

  Variable types : list type.

  (** this type requires decidable equality **)
  Inductive tvar : Type :=
  | tvProp 
  | tvType : nat -> tvar.

  Definition tvarD (x : tvar) := 
    match x with
      | tvProp => Prop
      | tvType x => 
        match nth_error types x with
          | None => Empty_set
          | Some t => Impl t
        end
    end.

  Definition typeFor (t : tvar) : type :=
    match t with
      | tvProp => {| Impl := Prop ; Eq := fun _ _ => None |}
      | tvType t => 
        match nth_error types t with
          | None => {| Impl := Empty_set ; Eq := fun x _ => match x with end |}
          | Some v => v 
        end
    end.

  Definition tvar_val_sdec (t : tvar) : forall (x y : tvarD t), option (x = y) :=
    match t as t return forall (x y : tvarD t), option (x = y) with
      | tvProp => fun _ _ => None
      | tvType t => 
        match nth_error types t as k return forall x y : match k with 
                                                           | None => Empty_set
                                                           | Some t => Impl t
                                                         end, option (x = y) with
          | None => fun x _ => match x with end
          | Some t => fun x y => match Eq t x y with
                                   | None => None
                                   | Some pf => Some pf
                                 end
        end

    end.

  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Record signature := Sig {
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

  Variable uenv : env.
  Variable env : env.

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

  Fixpoint exprD (e : expr) (t : tvar) : option (tvarD t) :=
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

  Fixpoint expr_seq_dec (a b : expr) : option (a = b) :=
    match a as a, b as b return option (a = b) with 
      | Const t c , Const t' c' =>
        match t as t , t' as t' return forall (c : tvarD t) (c' : tvarD t'), option (Const t c = Const t' c') with
          | tvType t , tvType t' =>
            match Peano_dec.eq_nat_dec t t' with
              | left pf => 
                match pf in _ = t' return forall (x : tvarD (tvType t)) (y : tvarD (tvType t')), 
                  option (Const (tvType t) x = Const (tvType t') y)
                  with
                  | refl_equal => fun x y =>
                    match tvar_val_sdec _ x y with
                      | None => None
                      | Some pf => Some (match pf in _ = z return Const (tvType t) x = Const (tvType t) z with
                                           | refl_equal => refl_equal
                                         end)  
                    end
                end 
              | right _ => fun _ _ => None
            end
          | _ , _ => fun _ _ => None
        end c c'
      | Var x , Var y => 
        match Peano_dec.eq_nat_dec x y with 
          | left pf => Some match pf in _ = t return Var x = Var t with
                              | refl_equal => refl_equal
                            end
          | right _ => None
        end
      | UVar x , UVar y => 
        match Peano_dec.eq_nat_dec x y with 
          | left pf => Some match pf in _ = t return UVar x = UVar t with
                              | refl_equal => refl_equal
                            end
          | right _ => None
        end
      | Func x xs , Func y ys =>
        match Peano_dec.eq_nat_dec x y with
          | left pf =>
            match (fix seq_dec' a b : option (a = b) :=
              match a as a, b as b return option (a = b) with
                | nil , nil => Some (refl_equal _)
                | x :: xs , y :: ys => 
                  match expr_seq_dec x y with
                    | None => None
                    | Some pf => 
                      match seq_dec' xs ys with
                        | None => None
                        | Some pf' => 
                          match pf in _ = t , pf' in _ = t' return option (x :: xs = t :: t') with
                            | refl_equal , refl_equal => Some (refl_equal _)
                          end
                      end
                  end
                | _ , _ => None
              end) xs ys with
              | None => None
              | Some pf' => Some (match pf in _ = t, pf' in _ = t' return Func x xs = Func t t' with
                                    | refl_equal , refl_equal => refl_equal
                                  end)
            end              
          | right _ => None
        end
      | _ , _ => None
    end.

  Global Instance SemiDec_expr : SemiDec expr := {| seq_dec := expr_seq_dec |}.

  (** lift the "real" variables in the range [a,...)
   ** to the range [a+b,...)
   **)
  Fixpoint liftExpr (a b : nat) (e : expr) : expr :=
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

  Fixpoint liftExprU (a b : nat) (e : expr (*(uvars' ++ uvars) vars*)) 
    : expr (*(uvars' ++ ext ++ uvars) vars*) :=
    match e with
      | UVar x => 
        if Compare_dec.lt_dec a x
        then UVar x
        else UVar (x + b)
      | Var v => Var v
      | Const t x => Const t x 
      | Func f xs => 
        Func f (map (liftExprU a b) xs)
    end.

  (** This function replaces "real" variables [a, b) with existential variables (c,...)
   **)
  Fixpoint exprSubstU (a b c : nat) (s : expr (*a (b ++ c ++ d)*)) {struct s}
      : expr (* (c ++ a) (b ++ d) *) :=
      match s with
        | Const _ t => Const _ t
        | Var x =>
          if Compare_dec.lt_dec x a 
          then Var x
          else if Compare_dec.lt_dec x b
               then UVar (c + x - a)
               else Var (x + a - b)
        | UVar x => UVar x
        | Func f args => Func f (map (exprSubstU a b c) args)
      end.

End env.

Implicit Arguments Const [ types t ].
Implicit Arguments Var [ types ].
Implicit Arguments UVar [ types ].
Implicit Arguments Func [ types ].