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

(** Base Types **)
(*
Inductive Typ :=
| List : Typ -> Typ
| Prod : Typ -> Typ -> Typ
| Nat  : Typ
.

Fixpoint denoteTyp (t : Typ) : Type :=
  match t with
    | List t => list (denoteTyp t)
    | Prod l r => denoteTyp l * denoteTyp r
    | Nat => nat
  end%type.

Definition Teq_dec : forall (t1 t2 : Typ), {t1 = t2} + {t1 <> t2}.
decide equality.
Defined.
*)

(** Syntax of Expressions **)
Class Typ : Type :=
{ type : Type }.

Section Expressions.
  Inductive Mem : list Typ -> Typ -> Type :=
  | MHere : forall T R, Mem (T :: R) T
  | MNext : forall T T' R, Mem R T -> Mem (T' :: R) T.

  Inductive Expr (G : list Typ) : Typ -> Type := 
  | Var   : forall T, Mem G T -> Expr G T
  | Const : forall T, @type T -> Expr G T
  | App   : c
    .
  | Pair : Expr -> Expr -> Expr
  | Cons : Expr -> Expr -> Expr
  | Nil  : Expr
  | Var  : nat -> Expr
    .

Section Context.
  Variable g : list { x : Typ & denoteTyp x }.

  Definition var_case (t : Typ) (n : nat) : option (denoteTyp t) :=
    match nth_error g n with
      | None => None
      | Some x => match Teq_dec (projT1 x) t with
                    | left pf => match pf with
                                   | refl_equal => Some (projT2 x)
                                 end
                    | right _ => None
                  end
    end.

  Fixpoint denoteExpr (t : Typ) (e : Expr) : option (denoteTyp t) :=
    match t as t return option (denoteTyp t) with
      | Nat => match e with
                 | Var n => var_case Nat n 
                 | NatI n => Some n
                 | _ => None
               end
      | List t' => match e with
                     | Var n => var_case (List t') n
                     | Nil => Some nil
                     | Cons l r => match denoteExpr t' l, denoteExpr (List t') r with
                                     | Some a , Some b => Some (a :: b)
                                     | _ , _ => None
                                   end
                     | _ => None
                   end
      | Prod t1 t2 => match e with
                        | Var n => var_case (Prod t1 t2) n
                        | Pair l r => 
                          match denoteExpr t1 l , denoteExpr t2 r with
                            | Some a , Some b => Some (a,b)
                            | _ , _ => None
                          end
                        | _ => None
                      end
    end.
End Context.

Definition Expr_dec (e1 e2 : Expr) : {e1 = e2} + {e1 <> e2}.
decide equality. decide equality. decide equality.
Defined.

(** Separation Formula Syntax **)
Fixpoint vaFun (ls : list Typ) (R : Type) : Type :=
  match ls with
    | nil => R
    | a :: b => denoteTyp a -> vaFun b R
  end.
Fixpoint vaApply (g : list { x : Typ & denoteTyp x }) {ls : list Typ} {R : Type} : vaFun ls R -> list Expr -> option R :=
  match ls as ls return vaFun ls R -> list Expr -> option R with
    | nil => fun f x => match x with 
                          | nil => Some f
                          | _ => None
                        end
    | t :: tr => fun f x => match x with
                              | nil => None
                              | v :: vr => match denoteExpr g t v with
                                             | None => None
                                             | Some v => @vaApply g tr R (f v) vr
                                           end
                            end
  end.

Record Terminal : Type :=
{ types : list Typ
; defn  : vaFun types sprop
}.

Inductive Sep :=
| Emp  : Sep                          (** empty heap **)
| Star : Sep -> Sep -> Sep            (** star **)
| ExS  : Sep -> Sep                   (** existential quantification over separation logic formula **)
| VarS : nat -> Sep                   (** variables of type separation logic formula **)
| ExE  : Typ -> Sep -> Sep            (** variables of expression types **)
| Term : string -> list Expr -> Sep   (** terminals **)
.

Section Denotation.
  Variable G : fmap string (fun _ => Terminal).

  Fixpoint Sep_denote (g : list sprop) (gv : list { x : Typ & denoteTyp x }) (s : Sep) : sprop :=
    match s with
      | Emp => semp
      | Star l r => star (Sep_denote g gv l) (Sep_denote g gv r)
      | Term t args => 
        match lookup _ _ string_dec t G with
          | None => fun _ => False
          | Some t =>
            match vaApply gv (@defn t) args with
              | None => fun _ => False
              | Some x => x
            end
        end
      | ExS b => fun h => exists x : sprop, Sep_denote (x :: g) gv b h
      | ExE t b => fun h => exists x : denoteTyp t, Sep_denote g (@existT _ (fun x => denoteTyp x) t x :: gv) b h
      | VarS n => match nth_error g n with
                    | None => fun _ => False
                    | Some x => x
                  end
    end.
End Denotation.

Definition Terminal_foo : Terminal :=
{| types := Nat :: nil 
 ; defn  := fun v => fun h => h v = Some v
|}.

Definition Terminal_bar : Terminal :=
{| types := nil 
 ; defn  := Sep_denote nil nil nil Emp
|}.

Definition Econs := insert string (fun _ => Terminal) string_dec.

(*
Eval compute in Sep_denote (Econs "foo" Terminal_foo (Econs "bar" Terminal_bar nil))%string nil nil
  (ExS (ExE Nat (Star (VarS 0) (Star (Term "foo" (Var 0 :: nil)) (Term "bar" nil))))).
*)








(*
Record SepState : Type :=
{ stars : mmap SepTerm vaFun ( }.

Parameter SepState_denote : SepState -> Prop.

Fixpoint reflect (s : Sep) (acc : SepState) : SepState :=
  match s with
    | Emp => acc
    | Start l r => 
      reflect r (reflect l acc)
    | App t a =>
  end.
*)