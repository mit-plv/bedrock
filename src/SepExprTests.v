Require Import Heaps.
Require SepExpr Expr.
Require Import EquivDec.
Require Import List.

Set Implicit Arguments.

Module SepExprTests (B : Heap).
  Module ST := SepTheoryX.SepTheoryX (B).
  Module Sep := SepExpr.SepExpr B ST.

  (** Just a test separation logic predicate **)
  Section Tests.
    Variable f : forall a b, nat -> ST.hprop a b nil.
    Variable h : forall a b, nat -> ST.hprop a b nil.
    Variable i : forall a b, nat -> ST.hprop a b nil.
    Variable g : bool -> nat -> nat -> nat.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Definition nat_type : Expr.type :=
      {| Expr.Impl := nat 
       ; Expr.Eq := fun x y => match equiv_dec x y with
                                 | left pf => Some pf
                                 | _ => None 
                               end
       |}.


    Fixpoint all a b (f : nat -> ST.hprop a b nil) (n : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f 0
        | S n => ST.star (f (S n)) (all f n)
      end.

    Fixpoint allb a b (f : nat -> ST.hprop a b nil) (n m : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f m
        | S n => ST.star (f (m - S n)) (allb f n m)
      end.

    Opaque ST.himp ST.star ST.emp ST.inj ST.ex.

    Goal forall a b c x y, @ST.himp a b c (f _ _ (g y (x + x) 1)) (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil) tt. 
    Abort.

    Goal forall a b c, 
      @ST.himp a b c (ST.star (allb (@h a b) 15 15) (allb (@f a b) 15 15))
                     (ST.star (all (@f a b) 15) (all (@h a b) 15)).
      simpl all. simpl allb.
      intros. Time Sep.sep isConst (nat_type :: nil) tt. reflexivity.
    Qed.

    Goal forall a b c, @ST.himp a b c 
      (ST.star (f _ _ 2) (f _ _ 1))
      (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil) tt.
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => ST.ex (fun x : bool => ST.star (f _ _ (g x 1 2)) (f _ _ 1) )))
      (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil) tt.
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => f _ _ y))
      (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil) tt.
    Abort.

  End Tests.

End SepExprTests.
