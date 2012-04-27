Require Import Heaps.
Require SepExpr Expr.
Require Import Provers.
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


    Fixpoint star_all a b (f : nat -> ST.hprop a b nil) (n : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f 0
        | S n => ST.star (f (S n)) (star_all f n)
      end.

    Fixpoint star_all_back a b (f : nat -> ST.hprop a b nil) (n m : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f m
        | S n => ST.star (f (m - S n)) (star_all_back f n m)
      end.

    Opaque ST.himp ST.star ST.emp ST.inj ST.ex.

    Import SepExpr Sep Expr ExprUnify DepList.

    Ltac simplifier := cbv beta iota zeta delta [CancelSep sepCancel hash hash' liftSHeap sheapSubstU liftExpr 
      SepExpr.FM.add SepExpr.FM.fold SepExpr.FM.map SepExpr.FM.find SepExpr.FM.remove
        SepExpr.FM.empty SepExpr.FM.insert_at_right
        other pures impures star_SHeap SHeap_empty
        unify_remove unify_remove_all exprUnifyArgs exprUnify empty_Subst Subst_lookup env_of_Subst
        Expr.Impl Expr.Eq
        List.map List.length List.app fold_left_2_opt List.fold_right List.nth_error
        starred sheapD exprD
        exprSubstU 
        Compare_dec.lt_eq_lt_dec Compare_dec.lt_dec Peano_dec.eq_nat_dec
        nat_rec nat_rect forallEach env exists_subst multimap_join equiv_dec seq_dec
        Domain Range
        EqDec_tvar tvar_rec tvar_rect 
        lookupAs sumbool_rec sumbool_rect
        fst snd
        eq_rec_r eq_rec eq_rect Logic.eq_sym f_equal get_Eq value 
        nat_eq_eqdec
        eq_summary eq_summarize eq_prove
        sexprD Compare_dec.le_dec Compare_dec.le_gt_dec Compare_dec.le_lt_dec
        Subst_replace plus minus substV

        transitivityEqProverRec groupsOf transitivityEqProver addEquality expr_seq_dec
        applyD
        in_seq_dec eqD_seq groupWith Expr.typeof unifyArgs inSameGroup fold_right
        bool_eqdec Bool.bool_dec bool_rec bool_rect

        nat_type
    ]; fold plus; fold minus.

    Ltac sep := simpl; intros;
      Sep.sep isConst transitivityEqProverRec simplifier (nat_type :: nil); try reflexivity.

    Goal forall a b c x y, @ST.himp a b c (f _ _ (g y (x + x) 1)) (f _ _ 1).
      sep.
    Abort.

    Theorem t1 : forall a b c, @ST.himp a b c (f _ _ 0) (f _ _ 0).
      sep.
    Qed.

    Theorem t2 : forall a b c, 
      @ST.himp a b c (ST.star (star_all_back (@h a b) 15 15) (star_all_back (@f a b) 15 15))
                     (ST.star (star_all (@f a b) 15) (star_all (@h a b) 15)).
      sep.
    Qed.

    Theorem t3 : forall a b c, @ST.himp a b c 
      (ST.star (f _ _ 2) (f _ _ 1))
      (f _ _ 1).
      sep.
    Abort.

    Theorem t4 : forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => ST.ex (fun x : bool => ST.star (f _ _ (g x 1 2)) (f _ _ 1) )))
      (f _ _ 1).
      sep.
    Abort.

    Theorem t5 : forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => f _ _ y))
      (f _ _ 1).
      sep.
    Abort.

    Theorem t6 : forall a b c, @ST.himp a b c 
      (f _ _ 1)
      (ST.ex (fun y : nat => f _ _ y)).
      sep.
    Qed.

    Theorem t7 : forall a b c, @ST.himp a b c 
      (ST.star (f _ _ (g true 0 1)) (f _ _ (g true 1 2)))
      (ST.ex (fun y : nat => ST.star (f _ _ (g true 0 y)) (ST.ex (fun z : nat => f _ _ (g true 1 z))))).
      sep.
    Qed.

    Theorem t8 : forall a b c, @ST.himp a b c 
      (ST.star (f _ _ (g true 0 1)) (f _ _ (g true 1 2)))
      (ST.ex (fun y : nat => ST.star (f _ _ (g true 1 y)) (ST.ex (fun z : nat => f _ _ (g true 0 z))))).
      sep.
    Qed.


    (** ** Test use of transitivity prover in cancellation *)

    Theorem t9 : forall a b c x y, x = y
      -> @ST.himp a b c  (f _ _ x) (f _ _ y).
      sep.
    Qed.

    Theorem t10 : forall a b c x y, x = y
      -> @ST.himp a b c  (f _ _ y) (f _ _ x).
      sep.
    Qed.

    Theorem t11 : forall a b c x y z, x = y
      -> x = z
      -> @ST.himp a b c  (f _ _ x) (f _ _ y).
      sep.
    Qed.

    Theorem t12 : forall a b c x y u v, x = y
      -> u = v
      -> @ST.himp a b c  (ST.star (f _ _ x) (f _ _ v)) (ST.star (f _ _ y) (f _ _ u)).
      sep.
    Qed.

    Theorem t13 : forall a b c x y z u v, x = y
      -> z = y
      -> u = v
      -> @ST.himp a b c  (ST.star (f _ _ x) (f _ _ v)) (ST.star (f _ _ z) (f _ _ u)).
      sep.
    Qed.

  End Tests.

End SepExprTests.
