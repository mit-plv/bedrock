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
End FunType.

(** Syntax of Expressions **)
Section Typed.
  Variable Typ : Type.

  Inductive Mem (T : Typ) : list Typ -> Type :=
  | MHere : forall R, Mem T (T :: R)
  | MNext : forall T' R, Mem T R -> Mem T (T' :: R)
  .

  Variable Sym : list Typ -> Typ -> Type.

  Inductive Expr (G : list Typ) : Typ -> Type := 
    (** TODO: This case doesn't really work b/c variables are not globally scoped.
     ** - This means that there essentially is not a way to compare two variables to see if they
     **   refer to the same variable.
     **)
  | Var  : forall T, Mem T G -> Expr G T
  | App0 : forall r (S : Sym nil r), Expr G r
  | App1 : forall {a1} {r} (S : Sym (a1 :: nil) r), 
    Expr G a1 -> Expr G r
  | App2 : forall {a1 a2} {r} (S : Sym (a1 :: a2 :: nil) r), 
    Expr G a1 -> Expr G a2 -> Expr G r
  | App3 : forall {a1 a2 a3} {r} (S : Sym (a1 :: a2 :: a3 :: nil) r), 
    Expr G a1 -> Expr G a2 -> Expr G a3 -> Expr G r
  | App4 : forall {a1 a2 a3 a4} {r} (S : Sym (a1 :: a2 :: a3 :: a4 :: nil) r), 
    Expr G a1 -> Expr G a2 -> Expr G a3 -> Expr G a4 -> Expr G r
  .

  Section Denote.
    Variable Sym_eq_dec : forall a b (l r : Sym a b), {l = r} + {l <> r}.
    Variable Typ_denote : Typ -> Type.
    Variable Sym_denote : forall a b (S : Sym a b), funtype Typ_denote a b.
    
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
        | App0 _ s => Sym_denote _ _ s
        | App1 _ _ s a => (Sym_denote _ _ s) (denoteExpr G E _ a)
        | App2 _ _ _ s a b => (Sym_denote _ _ s) (denoteExpr G E _ a) (denoteExpr G E _ b)
        | App3 _ _ _ _ s a b c => (Sym_denote _ _ s) (denoteExpr G E _ a) (denoteExpr G E _ b) (denoteExpr G E _ c)
        | App4 _ _ _ _ _ s a b c d => (Sym_denote _ _ s) (denoteExpr G E _ a) (denoteExpr G E _ b) (denoteExpr G E _ c) (denoteExpr G E _ d)
      end.
  
  End Denote.
End Typed.



Check App2.

Inductive Typ : Type := Nat.
Inductive Sym_nat : list Typ -> Typ -> Type :=
| Lit : nat -> Sym_nat nil Nat
| Plus : Sym_nat (Nat :: Nat :: nil) Nat
.

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

