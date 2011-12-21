Require Import Heaps.
Require Import SepExpr.
Require Import EquivDec.
Require Import List.

Set Implicit Arguments.

Module SepExpr (B : Heap).
  Module ST := SepTheoryX.SepTheoryX B.  
  Module Sep := SepExpr.SepExpr B.

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

    Definition nat_type : type :=
      {| Impl := nat 
       ; Eq := fun x y => match equiv_dec x y with
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


    Goal forall a b c, @ST.himp a b c (ST.star (allb (@h a b) 15 15) (allb (@f a b) 15 15)) (ST.star (all (@f a b) 15) (all (@h a b) 15)).
      simpl all. simpl allb.
      intros. Sep.reflect isConst (@nil type). 
      simple eapply ApplyCancelSep.
      lazy.
      reflexivity.
(*
      Transparent himp.
      unfold himp. simpl.
      Set Printing All.
      
       cbv beta iota zeta delta [CancelSep hash_left sepCancel].

      

(*      Time compute.
      Eval compute in (functionTypeD (map (@tvarD types) nil) (@tvarD types (Some (FS (FS FO))))).

      About Build_signature.
*)
      pose (types := (defaultType b :: defaultType a :: nat_type :: nil)).
      change (himp (types := types) (pcType := Some (FS FO)) (stateType := Some FO)
        (funcs := (Build_signature (types := types) nil (Some (FS (FS FO))) x :: (@nil (signature types))))
        (sfuncs := Build_ssignature (types := types) (Some (FS FO)) (Some FO) (Some (FS (FS FO)) :: nil) (f a b) :: nil)

        HNil HNil HNil c (Star Emp (Star Emp Emp)) (Star Emp (Star Emp Emp))).
      Set Printing All.
      

      
      
      

      Set Printing All
canceler.
      compute in H.
      match goal with 
        | [ |- @himp ?types ?funcs ?pcTyp ?stateTyp ?sfuncs _ _ _ _ _ _ ?cs ?L ?R ] =>
          let R := fresh in
            pose types ; pose funcs ;
              pose pcTyp ; pose stateTyp ; pose sfuncs ;
          pose (R := @CancelSep types funcs pcTyp stateTyp sfuncs cs nil L R)
      end.
      cbv beta iota zeta delta [CancelSep hash_left] in H.

      match eval unfold H in H with
        | ?X => idtac X
        | match ?X as p return _ with 
            | (_,_) => _
          end _ => idtac X
      end.

      pose (sepCancel (SHeap_empty nil nil nil (nil ++ nil))
              (liftSHeap nil nil nil
                 (sheapSubstU nil nil (SHeap_empty  l0 l1 nil (nil ++ nil))))).
      compute in p.

      Set Printing All.

      compute in H.
      hnf in H.
      simpl in H.
          let K := eval hnf in R in 
          match K with 
            | @Prove _ _ _ _ _ _ _ _ _ _ ?L' ?R' ?S ?PF =>
              simple eapply PF; unfold denote; simpl
          end



 canceler.
*)
    Abort.

    Goal forall a b c x y, @ST.himp a b c (f _ _ (g y (x + x) 1)) (f _ _ 1).
      intros. debug_reflect.
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.star (f _ _ 2) (f _ _ 1))
      (f _ _ 1).
      intros. debug_reflect.
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => ST.ex (fun x : bool => ST.star (f _ _ (g x 1 2)) (f _ _ 1) )))
      (f _ _ 1).
      intros. debug_reflect.
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => f _ _ y))
      (f _ _ 1).
      intros. debug_reflect.
    Abort.

  End Tests.