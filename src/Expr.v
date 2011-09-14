Require Import String.
Require Import Data List.
Require Import SepTheory.

Set Implicit Arugments.
Set Strict Implicit.

Fixpoint prod (ls : list Type) : Type :=
  match ls with
    | nil => unit
    | a :: b => a * prod b
  end%type.

Fixpoint prodN (T : Type) (n : nat) : Type :=
  match n with
    | 0 => unit
    | S n => T * prodN T n
  end%type.

Section FunType.
  Context {T : Type}.
  Variable D : T -> Type.

  Fixpoint funtype (ls : list T) (r : T) : Type :=
    match ls with 
      | nil => D r
      | a :: b => D a -> funtype b r
    end.

  (** This is a fixed point so coq unfolds it more often. **)
  Fixpoint funtype' (x : list T * T) {struct x} : Type :=
    match x with
      | (x,y) => funtype x y
    end.
End FunType.

(** Syntax of Expressions **)
Section Typed.
  Variable Typ : Type.

  Inductive Mem (T : Typ) : list Typ -> Type :=
  | MHere : forall R, Mem T (T :: R)
  | MNext : forall T' R, Mem T R -> Mem T (T' :: R)
  .

  Variable Sym : Type.
  Variable Sym_type : Sym -> list Typ * Typ.

  Inductive Expr (G : list Typ) : Typ -> Type := 
  | Var : forall T, Mem T G -> Expr G T
  | App : forall (S : Sym), Exprs G (fst (Sym_type S)) -> Expr G (snd (Sym_type S))
  with Exprs (G : list Typ) : list Typ -> Type :=
  | Enil  : Exprs G nil
  | Econs : forall T Ts, Expr G T -> Exprs G Ts -> Exprs G (T :: Ts)
  .

  Section Denote.
    Variable Sym_eq_dec : forall (l r : Sym), {l = r} + {l <> r}.
    Variable Typ_denote : Typ -> Type.
    Variable Sym_denote : forall (S : Sym), funtype Typ_denote (fst (Sym_type S)) (snd (Sym_type S)).
    
    Fixpoint Env (g : list Typ) : Type :=
      match g with
        | nil => unit
        | a :: b => Typ_denote a * Env b
      end%type.
    
    Fixpoint lookup T (g : list Typ) (m : Mem T g) : Env g -> Typ_denote T :=
      match m in Mem _ g return Env g -> Typ_denote T with
        | MHere _ => fun x => fst x
        | MNext _ _ r => fun x => lookup T _ r (snd x)
      end.

    Fixpoint denoteExpr G (E : Env G) (T : Typ) (e : Expr G T) : Typ_denote T :=
      match e in Expr _ T return Typ_denote T with
        | Var _ v => lookup _ G v E
        | App s es =>
          (fix denoteExprs Ts T (es : Exprs G Ts) : funtype Typ_denote Ts T -> Typ_denote T :=
            match es in Exprs _ Ts return funtype Typ_denote Ts T -> Typ_denote T with
              | Enil => fun r => r
              | Econs _ _ x y => fun f => denoteExprs _ _ y (f (denoteExpr G E _ x))
            end) (fst (Sym_type s)) (snd (Sym_type s)) es (Sym_denote s)
      end.
  
  End Denote.
End Typed.

Section Extensible.
  Definition Typ := nat.

(*
  Fixpoint Typ_eq_dec (a b : Typ) {struct a} : {a = b} + {a <> b}.
  decide equality.
  Defined.
*)

  Definition Typ_denote (f : Typ) : Type :=
    match f with
      | 0 => nat
      | _ => unit
    end.

  Inductive Nat_sym : Type :=
  | Nat : nat -> Nat_sym
  | Plus : Nat_sym.

  Definition Sym_type_Nat (x : Nat_sym) : list Typ * Typ :=
    match x with
      | Nat _ => (nil, 0)
      | Plus => (0 :: 0 :: nil, 0)
    end.

  Definition Sym_denote_nat (f : Nat_sym) : option (funtype' Typ_denote (Sym_type_Nat f)) :=
    match f with
      | Plus => Some plus
      | Nat i => Some i 
    end.

End Extensible.
(*
Check App2.

Ltac refl_nat e :=
  let rec refl e := 
    match e with
      | plus ?L ?R => 
        let l := refl L in
        let r := refl R in
        let r' := constr:(@App2 Typ Sym_nat nil Nat Nat Nat Plus l r) in r'
      | S _ => let r := constr:(@App0 _ _ nil Nat (Lit e)) in r
      | O => let r := constr:(@App0 _ _ nil Nat (Lit e)) in r
    end
  in 
  idtac e; 
  let res := refl e in
  idtac res;
  generalize (res).

Check map.

Fixpoint simplify_nat g (e : Expr Typ Sym_nat g Nat) {struct e} : Expr Typ Sym_nat g Nat :=
  match e return Expr Typ Sym_nat g Nat with
    | App2 _ _ _ c l r =>
      match c in Sym_nat T R return prod (@map Typ Type (Expr Typ Sym_nat g) T) -> Expr Typ Sym_nat g Nat with
        | Plus => fun lr =>
          let l := fst lr in
          let r := fst (snd lr) in
          match simplify_nat g l , simplify_nat g r return Expr Typ Sym_nat g Nat with
            | App0 _ (Lit l) , App0 _ (Lit r) => e (*App0 _ (Lit (l + r)) *)
            | l , r => e (*App2 _ _ _ Plus l r *)
          end
        | _ => fun _ => e
      end (l,(r,tt))
    | App0 _ (Lit _) => e 
    | _ => e
  end.


Goal 1 + 0 = 1.



match goal with 
  | [ |- ?X = ?Y ] => idtac X; refl_nat X
end.





refl_nat constr:(1).
*)