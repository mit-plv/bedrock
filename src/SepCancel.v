Require Import List.
Require Import SepTheoryX PropX.
Require Import PropXTac.
Require Import RelationClasses EqdepClass.
Require Import Expr ExprUnify.
Require Import SepExpr SepHeap.
Require Import Setoid.
Require Import Prover.
Require Import SepExpr.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (U : SynUnifier) (SH : SepHeap).
  Module Import SE := SH.SE.
  Module Import SEP_FACTS := SepExprFacts SE.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Variable funcs : functions types.
    Variable preds : SE.predicates types pcType stateType.

    (** The actual tactic code **)
    Variable Prover : ProverT types.
    Variable Prover_correct : ProverT_correct Prover funcs.

    Section fold_left3_opt.
      Variable T U V A : Type.
      Variable F : T -> U -> V -> A -> option A.

      Fixpoint fold_left_3_opt (ls : list T) (ls' : list U) (ls'' : list V) 
        (acc : A) : option A :=
        match ls, ls', ls'' with 
          | nil , nil , nil => Some acc
          | x :: xs , y :: ys , z :: zs => 
            match F x y z acc with
              | None => None
              | Some acc => fold_left_3_opt xs ys zs acc
            end
          | _ , _ , _ => None
        end.
    End fold_left3_opt.


    Definition unifyArgs (bound : nat) (summ : Facts Prover) (l r : list (expr types)) (ts : list tvar) (sub : U.Subst types)
      : option (U.Subst types) :=
      fold_left_3_opt 
        (fun l r t (acc : U.Subst _) =>
          if Prove Prover summ (Expr.Equal t l r)
            then Some acc
            else U.exprUnify bound l r acc)
        l r ts sub.

    Fixpoint unify_remove (bound : nat) (summ : Facts Prover) (l : exprs types) (ts : list tvar) (r : list (exprs types))
      (sub : U.Subst types)
      : option (list (list (expr types)) * U.Subst types) :=
        match r with 
          | nil => None
          | a :: b => 
            match unifyArgs bound summ l a ts sub with
              | None => 
                match unify_remove bound summ l ts b sub with
                  | None => None
                  | Some (x,sub) => Some (a :: x, sub)
                end
              | Some sub => Some (b, sub)
            end
        end.

    Require Ordering.

    Definition cancel_list : Type := 
      list (exprs types * nat).

    (** This function determines whether an expression [l] is more "defined"
     ** than an expression [r]. An expression is more defined if it "uses UVars later".
     ** NOTE: This is a "fuzzy property" but correctness doesn't depend on it.
     **)
    Fixpoint expr_count_meta (e : expr types) : nat :=
      match e with
        | Expr.Const _ _
        | Var _ => 0
        | UVar _ => 1
        | Not l => expr_count_meta l
        | Equal _ l r => expr_count_meta l + expr_count_meta r
        | Expr.Func _ args =>
          fold_left plus (map expr_count_meta args) 0
      end.

    Definition meta_order_args (l r : exprs types) : Datatypes.comparison :=
      let cmp l r := Compare_dec.nat_compare (expr_count_meta l) (expr_count_meta r) in
      Ordering.list_lex_cmp _ cmp l r.


    Definition meta_order_funcs (l r : exprs types * nat) : Datatypes.comparison :=
      match meta_order_args (fst l) (fst r) with
        | Datatypes.Eq => Compare_dec.nat_compare (snd l) (snd r)
        | x => x
      end.

    Definition order_impures (imps : MM.mmap (exprs types)) : cancel_list :=
      MM.FM.fold (fun k => fold_left (fun (acc : cancel_list) (args : exprs types) => 
        Ordering.insert_in_order _ meta_order_funcs (args, k) acc)) imps nil.

    Lemma impuresD'_flatten : forall U G cs imps,
      SE.heq funcs preds U G cs
        (SH.impuresD _ _ imps)
        (SH.starred (fun v => SE.Func (snd v) (fst v)) 
          (FM.fold (fun f argss acc => 
            map (fun args => (args, f)) argss ++ acc) imps nil) SE.Emp).
    Proof.
      clear. intros. eapply MM.PROPS.fold_rec; intros.
        rewrite (SH.impuresD_Empty funcs preds U G cs H).
        rewrite SH.starred_def. simpl. reflexivity.

        rewrite SH.impuresD_Add; eauto. rewrite SH.starred_app. 
        rewrite H2. symmetry. rewrite SH.starred_base. heq_canceler.
        repeat rewrite SH.starred_def.
        clear; induction e; simpl; intros; try reflexivity.
        rewrite IHe. reflexivity.
    Qed.

    Lemma starred_perm : forall T L R,
      Permutation.Permutation L R ->
      forall (F : T -> _) U G cs base,
      heq funcs preds U G cs (SH.starred F L base) (SH.starred F R base).
    Proof.
      clear. intros.
      repeat rewrite SH.starred_def.
      induction H; simpl; intros;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end; try reflexivity; heq_canceler.
    Qed.

    Lemma fold_Permutation : forall imps L R,
      Permutation.Permutation L R ->
      Permutation.Permutation
      (FM.fold (fun (f : FM.key) (argss : list (exprs types)) (acc : list (exprs types * FM.key)) =>
        map (fun args : exprs types => (args, f)) argss ++ acc) imps L)
      (MM.FM.fold
        (fun k : MM.FM.key =>
         fold_left
           (fun (acc : cancel_list) (args : exprs types) =>
            Ordering.insert_in_order (exprs types * nat) meta_order_funcs
              (args, k) acc)) imps R).
    Proof.
      clear. intros.
      eapply @MM.PROPS.fold_rel; simpl; intros; auto.
        revert H1; clear. revert a; revert b; induction e; simpl; intros; auto.
        rewrite <- IHe; eauto.
        
        destruct (@Ordering.insert_in_order_inserts (exprs types * nat) meta_order_funcs (a,k) b) as [ ? [ ? [ ? ? ] ] ].
        subst. rewrite H.
        rewrite <- app_ass.
        eapply Permutation.Permutation_cons_app.
        rewrite app_ass. eapply Permutation.Permutation_app; eauto.
    Qed.

    Lemma order_impures_D : forall U G cs imps,
      heq funcs preds U G cs 
        (SH.impuresD _ _ imps)
        (SH.starred (fun v => (Func (snd v) (fst v))) (order_impures imps) Emp).
    Proof.
      clear. intros. rewrite impuresD'_flatten. unfold order_impures.
      eapply starred_perm. eapply fold_Permutation. reflexivity.
    Qed.
    
    (** NOTE : l and r are reversed here **)
    Fixpoint cancel_in_order (bound : nat) (summ : Facts Prover) 
      (ls : cancel_list) (acc rem : MM.mmap (exprs types)) (sub : U.Subst types) 
      : MM.mmap (exprs types) * MM.mmap (exprs types) * U.Subst types :=
      match ls with
        | nil => (acc, rem, sub)
        | (args,f) :: ls => 
          match MM.FM.find f rem with
            | None => cancel_in_order bound summ ls (MM.mmap_add f args acc) rem sub
            | Some argss =>
              match nth_error preds f with
                | None => cancel_in_order bound summ ls (MM.mmap_add f args acc) rem sub (** Unused! **)
                | Some ts => 
                  match unify_remove bound summ args (SDomain ts) argss sub with
                    | None => cancel_in_order bound summ ls (MM.mmap_add f args acc) rem sub
                    | Some (rem', sub) =>
                      cancel_in_order bound summ ls acc (MM.FM.add f rem' rem) sub
                  end
              end                      
          end
      end.

    Lemma cancel_in_orderOk : forall U G cs bound summ ls acc rem sub L R S,
      cancel_in_order bound summ ls acc rem sub = (L, R, S) ->
      himp funcs preds U G cs (SH.impuresD _ _ R) (SH.impuresD _ _ L) ->
      himp funcs preds U G cs 
        (SH.impuresD _ _ acc)
        (Star (SH.starred (fun v => (Func (snd v) (fst v))) ls Emp)
              (SH.impuresD _ _ acc)).
    Proof.
      
    Admitted.


    Definition sepCancel (bound : nat) (summ : Facts Prover) (l r : SH.SHeap types pcType stateType) :
      SH.SHeap _ _ _ * SH.SHeap _ _ _ * U.Subst types :=
      let ordered_r := order_impures (SH.impures r) in
      let sorted_l := MM.FM.map (fun v => Ordering.sort _ meta_order_args v) (SH.impures l) in 
      let '(rf, lf, sub) := 
        cancel_in_order bound summ ordered_r (MM.empty _) sorted_l (U.Subst_empty _)
      in
      ({| SH.impures := lf ; SH.pures := SH.pures l ; SH.other := SH.other l |},
       {| SH.impures := rf ; SH.pures := SH.pures r ; SH.other := SH.other r |},
       sub).

    Theorem sepCancel_correct : forall U G cs bound summ l r l' r' sub,
      Valid Prover_correct U G summ ->
      sepCancel bound summ l r = (l', r', sub) ->
      himp funcs preds U G cs (SH.sheapD l) (SH.sheapD r) ->
      U.Subst_equations funcs U G sub ->
      himp funcs preds U G cs (SH.sheapD l') (SH.sheapD r').
    Proof.
      clear. destruct l; destruct r. unfold sepCancel. simpl.
      intros. repeat rewrite sheapD_sheapD'. repeat rewrite sheapD_sheapD' in H1.
      destruct l'; destruct r'. 

      
    Admitted.

  End env.

End Make.
