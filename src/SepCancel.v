Require Import List.
Require Import SepTheoryX PropX.
Require Import PropXTac.
Require Import RelationClasses EqdepClass.
Require Import Expr ExprUnify.
Require Import SepExpr SepHeap.
Require Import Setoid.
Require Import Prover.
Require Import SepExpr.
Require Import Folds.
Require Import Reflection.

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


    Definition unifyArgs (bound : nat) (summ : Facts Prover) (l r : list (expr types)) (ts : list tvar) (sub : U.Subst types)
      : option (U.Subst types) :=
      Folds.fold_left_3_opt 
        (fun l r t (acc : U.Subst _) =>
          if Prove Prover summ (Expr.Equal t (U.exprInstantiate acc l) (U.exprInstantiate acc r))
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
    
    Section with_typing.
      Variable tfuncs : tfunctions.
      Variables tU tG : tenv.
      Variables U G : env types.

      Hypothesis WT_funcs : WellTyped_funcs tfuncs funcs.
      Hypothesis WT_env_U : WellTyped_env tU U.
      Hypothesis WT_env_G : WellTyped_env tG G.

      Lemma unifyArgs_Extends_WellTyped : forall bound summ l r ts S S',
        U.Subst_WellTyped tfuncs tU tG S ->
        Valid Prover_correct U G summ ->
        all2 (@is_well_typed _ tfuncs tU tG) l ts = true ->
        all2 (@is_well_typed _ tfuncs tU tG) r ts = true ->
        unifyArgs bound summ l r ts S = Some S' ->
        U.Subst_Extends S' S /\
        U.Subst_WellTyped tfuncs tU tG S'.
      Proof.
        unfold unifyArgs; induction l; destruct r; destruct ts; simpl; intros; try congruence.
        { inversion H2. inversion H3; subst; intuition; auto. }
        { repeat match goal with
          | [ H : (if ?X then _ else _) = true |- _ ] =>
            revert H; case_eq X; intros; [ | congruence ]
                   | [ |- context [ exprD ?A ?B ?C ?D ?E ] ] =>
                     case_eq (exprD A B C D E); intros
                 end; simpl in *;
        try solve [ 
          match goal with
            | [ H : is_well_typed _ _ _ ?e _ = true , H' : exprD _ _ _ (U.exprInstantiate ?S' ?e) _ = None |- _ ] =>
              exfalso; revert H; revert H'; clear; intros H' H;
                eapply WellTyped_exprInstantiate with (S := S') in H;
                  eapply is_well_typed_correct in H;
                    rewrite H' in H ; destruct H; congruence
          end ].
          revert H3. case_eq (Prove Prover summ (Equal t (U.exprInstantiate S a) (U.exprInstantiate S e))); simpl; eauto.
          case_eq (U.exprUnify bound a e S); intros; try congruence.
          eapply IHl in H7; eauto using U.exprUnify_WellTyped.
          intuition. etransitivity; eauto using U.exprUnify_Extends. }
      Qed.          

      Lemma unifyArgs_bad_cases : forall summ bound S S' ts t e a l r,
        U.Subst_WellTyped tfuncs tU tG S ->
        Valid Prover_correct U G summ ->
        all2 (@is_well_typed _ tfuncs tU tG) l ts = true ->
        all2 (@is_well_typed _ tfuncs tU tG) r ts = true ->
        @is_well_typed _ tfuncs tU tG a t = true ->
        @is_well_typed _ tfuncs tU tG e t = true ->
        match
          (if Prove Prover summ
            (Equal t (U.exprInstantiate S a) (U.exprInstantiate S e))
            then Some S
            else U.exprUnify bound a e S)
          with
          | Some acc =>
            fold_left_3_opt
            (fun (l r : expr types) (t : tvar) (acc0 : U.Subst types) =>
              if Prove Prover summ
                (Equal t (U.exprInstantiate acc0 l)
                  (U.exprInstantiate acc0 r))
                then Some acc0
                else U.exprUnify bound l r acc0) l r ts acc
          | None => None
        end = Some S' ->
        U.Subst_Extends S' S /\ U.Subst_WellTyped tfuncs tU tG S'.
      Proof.
        intros. destruct (Prove Prover summ (Equal t (U.exprInstantiate S a) (U.exprInstantiate S e))).
        apply unifyArgs_Extends_WellTyped in H5; eauto; intuition.
        revert H5. case_eq (U.exprUnify bound a e S); intros; eauto.
        generalize H5. eapply U.exprUnify_Extends in H5.
        intro. eapply U.exprUnify_WellTyped in H7; eauto.
        eapply unifyArgs_Extends_WellTyped in H6; eauto; intuition.
        etransitivity; eauto. 
        congruence.
      Qed.

      Lemma unifyArgsOk : forall bound summ R l r ts f S S',
        U.Subst_WellTyped tfuncs tU tG S ->
        Valid Prover_correct U G summ ->
        all2 (@is_well_typed _ tfuncs tU tG) l ts = true ->
        all2 (@is_well_typed _ tfuncs tU tG) r ts = true ->
        unifyArgs bound summ l r ts S = Some S' ->
        U.Subst_equations funcs U G S' ->
        @applyD types (exprD funcs U G) ts (map (U.exprInstantiate S') l) R f =
        @applyD types (exprD funcs U G) ts (map (U.exprInstantiate S') r) R f /\
        U.Subst_Extends S' S /\
        U.Subst_WellTyped tfuncs tU tG S'.
      Proof.
        unfold unifyArgs; induction l; destruct r; destruct ts; simpl; intros; try congruence.
        { inversion H2. inversion H3; subst; intuition; auto. }
        { repeat match goal with
          | [ H : (if ?X then _ else _) = true |- _ ] =>
            revert H; case_eq X; intros; [ | congruence ]
                   | [ |- context [ exprD ?A ?B ?C ?D ?E ] ] =>
                     case_eq (exprD A B C D E); intros
                 end; simpl in *;
        try solve [ 
          match goal with
            | [ H : is_well_typed _ _ _ ?e _ = true , H' : exprD _ _ _ (U.exprInstantiate ?S' ?e) _ = None |- _ ] =>
              exfalso; revert H; revert H'; clear; intros H' H;
                eapply WellTyped_exprInstantiate with (S := S') in H;
                  eapply is_well_typed_correct in H;
                    rewrite H' in H ; destruct H; congruence
          end ].
          revert H3. case_eq (Prove Prover summ (Equal t (U.exprInstantiate S a) (U.exprInstantiate S e))); intros.
          { eapply Prove_correct in H3; eauto.
            erewrite U.exprInstantiate_WellTyped in H2 by eauto.
            erewrite U.exprInstantiate_WellTyped in H1 by eauto.
            eapply is_well_typed_correct in H2; eauto.
            eapply is_well_typed_correct in H1; eauto.
            destruct H2; destruct H1.
            unfold ValidProp, Provable in *. simpl in *.
            repeat match goal with 
                     | [ H : _ = _ |- _ ] => rewrite H in *
                     | [ H : ?X -> ?Y |- _ ] => 
                       let H' := fresh in assert (H':X) by eauto; specialize (H H')
                   end.
            subst.
            eapply IHl with (f := f t0) in H9; eauto.
            intuition. rewrite H3. f_equal. f_equal.
            erewrite U.Subst_equations_exprInstantiate in H2 by eauto.
            erewrite U.Subst_equations_exprInstantiate in H1 by eauto.
            rewrite U.exprInstantiate_Extends in H2 by eauto.
            rewrite U.exprInstantiate_Extends in H1 by eauto.
            rewrite H2 in H8. rewrite H1 in H7. inversion H7; inversion H8; subst; auto. }
          { clear H3. revert H9. case_eq (U.exprUnify bound a e S); intros; try congruence.
            eapply IHl with (f := f t0) in H9; eauto using U.exprUnify_WellTyped.
            intuition. rewrite H10. f_equal. f_equal.
            eapply U.exprUnify_sound in H3. 
            assert (U.exprInstantiate S' (U.exprInstantiate s a) = U.exprInstantiate S' (U.exprInstantiate s e)).
            rewrite H3; auto.
            repeat rewrite U.exprInstantiate_Extends in H11 by eauto. rewrite H11 in H7. rewrite H7 in H8. inversion H8; auto.

            etransitivity; eauto using U.exprUnify_Extends. }
          { exfalso.
            eapply unifyArgs_bad_cases in H3; eauto; intuition.
            do 2 match goal with
              | [ H : is_well_typed _ _ _ ?E _ = true ,
                  H' : exprD _ _ _ ?E _ = None |- _ ] =>
              (eapply is_well_typed_correct in H ; eauto) ; destruct H; congruence
              | [ H : exprD _ _ _ ?E _ = None |- _ ] =>
                assert (@is_well_typed _ tfuncs tU tG E t = true) by 
                  (rewrite <- U.exprInstantiate_WellTyped; eauto)
            end. }
          { exfalso.
            eapply unifyArgs_bad_cases in H3; eauto; intuition.
            do 2 match goal with
              | [ H : is_well_typed _ _ _ ?E _ = true ,
                  H' : exprD _ _ _ ?E _ = None |- _ ] =>
              (eapply is_well_typed_correct in H ; eauto) ; destruct H; congruence
              | [ H : exprD _ _ _ ?E _ = None |- _ ] =>
                assert (@is_well_typed _ tfuncs tU tG E t = true) by 
                  (rewrite <- U.exprInstantiate_WellTyped; eauto)
            end. }
          { exfalso.
            eapply unifyArgs_bad_cases in H3; eauto; intuition.
            do 2 match goal with
              | [ H : is_well_typed _ _ _ ?E _ = true ,
                  H' : exprD _ _ _ ?E _ = None |- _ ] =>
              (eapply is_well_typed_correct in H ; eauto) ; destruct H; congruence
              | [ H : exprD _ _ _ ?E _ = None |- _ ] =>
                assert (@is_well_typed _ tfuncs tU tG E t = true) by 
                  (rewrite <- U.exprInstantiate_WellTyped; eauto)
            end. } }
      Qed.

      Lemma WellTyped_exprInstantiate_applyD : forall S',
        U.Subst_equations funcs U G S' ->
        forall p l,
          applyD (exprD funcs U G) (SDomain p) l
          (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
          (SDenotation p) =
          applyD (exprD funcs U G) (SDomain p) (map (U.exprInstantiate S') l)
          (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
          (SDenotation p).
      Proof.
        clear. destruct p. induction SDomain0; destruct l; simpl; auto.
        rewrite <- U.Subst_equations_exprInstantiate; eauto.
        destruct (exprD funcs U G e a); eauto.
      Qed.
      
      Lemma unify_removeOk : forall cs bound summ f p l S,
        U.Subst_WellTyped tfuncs tU tG S ->
        Valid Prover_correct U G summ ->
        nth_error preds f = Some p ->
        all2 (@is_well_typed _ tfuncs tU tG) l (SDomain p) = true ->
        forall r r' S' P,
          List.Forall (fun r => all2 (@is_well_typed _ tfuncs tU tG) r (SDomain p) = true) r ->
          unify_remove bound summ l (SDomain p) r S = Some (r', S') ->
          U.Subst_equations funcs U G S' ->
          forall Q,
          SE.heq funcs preds U G cs P (SH.starred (SE.Func f) r' Q) ->
          SE.heq funcs preds U G cs
            (SE.Star (SE.Func f l) P) (SH.starred (SE.Func f) r Q) /\
          U.Subst_Extends S' S.
      Proof.
(*        do 12 intro.  
        match goal with
          | [ |- context [ @Emp ?X ?Y ?Z ] ] => generalize (@Emp X Y Z)
        end.
*)
        induction r; simpl; intros; try congruence.
        revert H4. case_eq (unifyArgs bound summ l a (SDomain p) S); intros; try congruence.
        { inversion H7; clear H7; subst.
          inversion H3; clear H3; subst.
          rewrite SH.starred_def. simpl. rewrite <- SH.starred_def.
          eapply unifyArgsOk with (R := ST.hprop (tvarD types pcType) (tvarD types stateType) nil) (f := SDenotation p) in H4;
            eauto. 
          intuition.
          apply heq_star_frame; auto. unfold heq; simpl. rewrite H1.
          match goal with
            | [ |- ST.heq _ match ?X with _ => _ end match ?Y with _ => _ end ] =>
              cutrewrite (X = Y)
          end. reflexivity.
          revert H3. repeat rewrite <- WellTyped_exprInstantiate_applyD; eauto. }
        { revert H7. case_eq (unify_remove bound summ l (SDomain p) r S); intros; try congruence.
          destruct p0. inversion H8; clear H8; subst. clear H4.
          inversion H3; clear H3; subst.
          rewrite SH.starred_def in H6. simpl in H6. rewrite <- SH.starred_def in H6.
          eapply IHr in H7; eauto.
          Focus 2. instantiate (1 := (SH.SE.Star (Func f a) Q)). instantiate (1 := P).
          etransitivity. eapply H6. rewrite SH.starred_base. symmetry. rewrite SH.starred_base.
          heq_canceler.
          intuition. rewrite SH.starred_def. simpl. rewrite <- SH.starred_def.
          rewrite H3. rewrite SH.starred_base. symmetry. rewrite SH.starred_base. heq_canceler. }
      Qed.
    End with_typing.

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
      FM.fold (fun k => fold_left (fun (acc : cancel_list) (args : exprs types) => 
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
      (FM.fold
        (fun k : FM.key =>
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
          match FM.find f rem with
            | None => cancel_in_order bound summ ls (MM.mmap_add f args acc) rem sub
            | Some argss =>
              match nth_error preds f with
                | None => cancel_in_order bound summ ls (MM.mmap_add f args acc) rem sub (** Unused! **)
                | Some ts => 
                  match unify_remove bound summ args (SDomain ts) argss sub with
                    | None => cancel_in_order bound summ ls (MM.mmap_add f args acc) rem sub
                    | Some (rem', sub) =>
                      cancel_in_order bound summ ls acc (FM.add f rem' rem) sub
                  end
              end                      
          end
      end.
    
    Definition sheapInstantiate (s : U.Subst types) : MM.mmap (exprs types) -> MM.mmap (exprs types) :=
      MM.mmap_map (map (@U.exprInstantiate _ s)).

    Lemma sheapInstantiate_mmap_add : forall U G cs S n e acc,
      heq funcs preds U G cs
        (SH.impuresD pcType stateType 
          (sheapInstantiate S (MM.mmap_add n e acc)))
        (SH.impuresD pcType stateType 
          (MM.mmap_add n (map (@U.exprInstantiate _ S) e) 
                         (sheapInstantiate S acc))).
    Proof.
      clear. intros. eapply MM.PROPS.map_induction with (m := acc); intros.
      { unfold MM.mmap_add, sheapInstantiate, MM.mmap_map.
        repeat rewrite MF.find_Empty by auto using MF.map_Empty.
        rewrite SH.impuresD_Equiv. reflexivity.
        rewrite MF.map_add. simpl.
        reflexivity. }
      { unfold MM.mmap_add, sheapInstantiate, MM.mmap_map.
        rewrite MF.FACTS.map_o. simpl in *. unfold exprs in *. case_eq (FM.find n m'); simpl; intros.
        { rewrite SH.impuresD_Equiv. reflexivity.
          rewrite MF.map_add. reflexivity. }
        { rewrite SH.impuresD_Equiv. reflexivity.
          rewrite MF.map_add. simpl. reflexivity. } }
    Qed.

    Lemma sheapInstantiate_Equiv : forall S a b,
      MM.mmap_Equiv a b ->
      MM.mmap_Equiv (sheapInstantiate S a) (sheapInstantiate S b).
    Proof.
      clear. unfold sheapInstantiate, MM.mmap_Equiv, MM.mmap_map, FM.Equiv; intuition;
      try solve [ repeat match goal with
                           | [ H : FM.In _ (FM.map _ _) |- _ ] => apply MF.FACTS.map_in_iff in H
                           | [ |- FM.In _ (FM.map _ _) ] => apply MF.FACTS.map_in_iff
                         end; firstorder ].
      repeat match goal with
               | [ H : FM.MapsTo _ _ (FM.map _ _) |- _ ] =>
                 apply MF.FACTS.map_mapsto_iff in H; destruct H; intuition; subst
             end.
      apply Permutation.Permutation_map. firstorder.
    Qed.

    Lemma cancel_in_order_equiv : forall bound summ ls acc rem sub L R S acc',
      MM.mmap_Equiv acc acc' ->
      cancel_in_order bound summ ls acc rem sub = (L, R, S) ->
      exists L' R' S',
        cancel_in_order bound summ ls acc' rem sub = (L', R', S') /\
        MM.mmap_Equiv L L' /\
        MM.mmap_Equiv R R' /\
        U.Subst_Equal S S'.
    Proof.
      clear. induction ls; simpl; intros.
      { inversion H0; subst; auto. 
        do 3 eexists. split; [ reflexivity | intuition ]. }
      { repeat match goal with
                 | [ H : match ?X with 
                           | (_,_) => _
                         end = _ |- _ ] => destruct X
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 revert H; case_eq X; intros
                 
               end;
        (eapply IHls; [ eauto using MM.mmap_add_mor | eassumption ]). }
    Qed.

    Lemma cancel_in_order_mmap_add_acc : forall bound summ ls n e acc rem sub L R S,
      cancel_in_order bound summ ls (MM.mmap_add n e acc) rem sub = (L, R, S) ->
      exists L' R' S',
        cancel_in_order bound summ ls acc rem sub = (L', R', S') /\
        MM.mmap_Equiv (MM.mmap_add n e L') L /\
        MM.mmap_Equiv R R' /\
        U.Subst_Equal S S'.
    Proof.
      clear. induction ls; simpl; intros.
      { inversion H; subst. do 3 eexists; split. 
        reflexivity. split; try reflexivity. split; try reflexivity. }
      { repeat match goal with
                 | [ H : match ?X with 
                           | (_,_) => _
                         end = _ |- _ ] => destruct X
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 revert H; case_eq X; intros
                 
               end;
        try solve [ eapply IHls; eauto ];
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ = _ |- _ ] =>
            eapply cancel_in_order_equiv in H; [ | eapply MM.mmap_add_comm ]
        end;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
               end;
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ = _ |- _ ] =>
            eapply IHls in H
        end;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ |- exists x, _ /\ _ ] => eexists; split; [ eassumption | ]
                 | [ |- exists x, _ ] => eexists
                 | [ H : MM.mmap_Equiv _ _ |- _ ] => rewrite H
                 | [ H : U.Subst_Equal _ _ |- _ ] => rewrite H
               end; intuition reflexivity. }
    Qed.

(*
    Lemma cancel_in_order_add_acc : forall bound summ ls n e acc rem sub L R S,
      ~FM.In n acc ->
      cancel_in_order bound summ ls (FM.add n e acc) rem sub = (L, R, S) ->
      exists L' R' S',
        cancel_in_order bound summ ls acc rem sub = (L', R', S') /\
        MM.mmap_Equiv (FM.add n e L') L /\
        MM.mmap_Equiv R R' /\
        U.Subst_Equal S S'.
    Proof.
      clear. induction ls; simpl; intros.
      { inversion H0; subst. do 3 eexists; split. 
        reflexivity. split; try reflexivity. split; try reflexivity. }
      { repeat match goal with
                 | [ H : match ?X with 
                           | (_,_) => _
                         end = _ |- _ ] => destruct X
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 revert H; case_eq X; intros
                 
               end;
        try solve [ eapply IHls; eauto |
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ = _ |- _ ] =>
            eapply cancel_in_order_equiv in H; [ | eapply MM.mmap_add_comm ]
        end;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
               end;
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ = _ |- _ ] =>
            eapply IHls in H
        end;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ |- exists x, _ /\ _ ] => eexists; split; [ eassumption | ]
                 | [ |- exists x, _ ] => eexists
                 | [ H : MM.mmap_Equiv _ _ |- _ ] => rewrite H
                 | [ H : U.Subst_Equal _ _ |- _ ] => rewrite H
               end; intuition reflexivity ].
        Focus 3.
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ = _ |- _ ] =>
            eapply cancel_in_order_equiv in H; [ | ]
        end.
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
               end;
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ = _ |- _ ] =>
            eapply IHls in H
        end.



 }
    Qed.
*)

    Lemma sheapInstantiate_add : forall U G cs S n e m m',
      ~FM.In n m ->
      MM.PROPS.Add n e m m' ->
      heq funcs preds U G cs
        (SH.impuresD pcType stateType (sheapInstantiate S m'))
        (SH.starred (fun v => Func n (map (U.exprInstantiate S) v)) e
          (SH.impuresD pcType stateType (sheapInstantiate S m))).
    Proof.
      clear. intros.
        unfold sheapInstantiate, MM.mmap_map.
        rewrite SH.impuresD_Add with (i := FM.map (map (map (U.exprInstantiate S))) m) (f := n) (argss := map (map (U.exprInstantiate S)) e).
        symmetry; rewrite SH.starred_base. heq_canceler.
        repeat rewrite SH.starred_def.
        match goal with
          | [ |- context [ @SH.SE.Emp ?X ?Y ?Z ] ] => generalize (@SH.SE.Emp X Y Z)
        end.
        clear. induction e; simpl; intros; try reflexivity.
        rewrite IHe. heq_canceler.

        red. intros. specialize (H0 y). repeat (rewrite MM.FACTS.add_o in * || rewrite MM.FACTS.map_o in * ).
        unfold exprs in *. rewrite H0. unfold MM.FACTS.option_map. destruct (MF.FACTS.eq_dec n y); auto.
        
        intro. apply H. apply MM.FACTS.map_in_iff in H1. auto.
    Qed.

    Lemma cancel_in_orderOk : forall tU tG tfuncs U G cs bound summ,
      WellTyped_env tU U ->
      WellTyped_env tG G ->
      WellTyped_funcs tfuncs funcs ->
      forall ls acc rem sub L R S Q,
      U.Subst_WellTyped tfuncs tU tG sub ->
      U.Subst_equations funcs U G S ->
      Valid Prover_correct U G summ ->
      cancel_in_order bound summ ls acc rem sub = (L, R, S) ->
      himp funcs preds U G cs 
        (SH.impuresD _ _ (sheapInstantiate S R))
        (Star (SH.impuresD _ _ (sheapInstantiate S L)) Q) ->
      himp funcs preds U G cs 
        (SH.impuresD _ _ (sheapInstantiate S rem))
        (Star (Star (SH.starred (fun v => (Func (snd v) (map (@U.exprInstantiate _ S) (fst v)))) ls Emp)
                    (SH.impuresD _ _ (sheapInstantiate S acc)))
              Q).
    Proof.
      induction ls; simpl; intros.
      { inversion H5; clear H5; subst.
        rewrite SH.starred_def. simpl. heq_canceler. auto. }
      { rewrite SH.starred_def. simpl. rewrite <- SH.starred_def.
        repeat match goal with
                 | [ H : match ?X with 
                           | (_,_) => _
                         end = _ |- _ ] => destruct X
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 revert H; case_eq X; intros
               end.
        { (* (eapply unify_removeOk with (cs := cs) 
            (P := Star (SH.impuresD pcType stateType (sheapInstantiate S acc))
              (SH.starred
                (fun x : list (expr types) * func =>
                  Func (snd x) (map (U.exprInstantiate S) (fst x))) ls Emp)) in H8;
            [ | | | | eassumption | | | | | | ]); try eassumption. *)
          Lemma cancel_in_order_add_rem : forall cs U G funcs preds bound summ ls n e acc rem sub L R S l,
            FM.find n rem = Some l ->
            cancel_in_order bound summ ls acc (FM.add n e rem) sub = (L, R, S) ->
            forall P Q,
            heq funcs preds U G cs 
              (SH.starred (Func n) e P) 
              (SH.starred (Func n) l Q) -> (* L, R? *)
            heq funcs preds U G cs
              (Star (SH.impuresD pcType stateType (FM.add n e rem)) P)
              (Star (SH.starred (fun x => Func (snd x) (map (U.exprInstantiate S) (fst x))) ls (SH.impuresD _ _ acc)) Q).
          Proof.
            induction ls; simpl; intros.
            { rewrite SH.starred_def. simpl. admit. }
          Abort.
          admit. }
        { eapply cancel_in_order_mmap_add_acc in H9.
          do 3 destruct H9. intuition.
          eapply IHls in H10; eauto. simpl. rewrite SEP_FACTS.heq_star_assoc.
          Focus 3. instantiate (1 := Star (Func n e) Q). admit.
          admit. admit. }
        { Lemma impuresD_remove_sheapInstantiate : forall U G S cs h,
            U.Subst_equations funcs U G S ->
            heq funcs preds U G cs 
              (SH.impuresD pcType stateType (sheapInstantiate S h))
              (SH.impuresD pcType stateType h).
          Proof.
            clear. admit.
          Qed.
          repeat rewrite impuresD_remove_sheapInstantiate by auto.
          eapply cancel_in_order_mmap_add_acc in H8; eauto. do 3 destruct H8. intuition.
          eapply IHls in H9; eauto. 
          Focus 3. instantiate (1 := Star Q (Func n e)). repeat rewrite impuresD_remove_sheapInstantiate.
          admit. admit. admit.
          rewrite impuresD_remove_sheapInstantiate in H9.
          rewrite impuresD_remove_sheapInstantiate in H9.
          admit.
          admit.
          admit.
          admit. }
        { admit. (** same proof as above **) }
    Qed.


    Definition sepCancel (bound : nat) (summ : Facts Prover) (l r : SH.SHeap types pcType stateType) :
      SH.SHeap _ _ _ * SH.SHeap _ _ _ * U.Subst types :=
      let ordered_r := order_impures (SH.impures r) in
      let sorted_l := FM.map (fun v => Ordering.sort _ meta_order_args v) (SH.impures l) in 
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
