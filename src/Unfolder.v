Require Import Arith Bool EqdepClass List.

Require Import Heaps (* Reflect *).
Require Import Expr ExprUnify Folds.
Require Import SepExpr SepHeap.
Require Import Prover.
Require Import Env.
Require Import Reflection.

Set Implicit Arguments.

Require NatMap.

Module FM := NatMap.IntMap.

Fixpoint allb A (P : A -> bool) (ls : list A) : bool :=
  match ls with
    | nil => true
    | x :: ls' => P x && allb P ls'
  end.

Module Make (SH : SepHeap) (U : SynUnifier).
  Module Import SE := SH.SE.
  Import SH.
  Module HEAP_FACTS := SepHeapFacts SH.
  Import HEAP_FACTS.
  Module ST_EXT := SepTheoryX.SepTheoryX_Ext SE.ST.
  
  Module B := SE.ST.H.

  Section env.
    Variable types : list type.
    Variable funcs : functions types.
    
    Variable pcType : tvar.
    Variable stateType : tvar.
    Variable stateMem : tvarD types stateType -> B.mem.

    Variable preds : predicates types pcType stateType.

    (** * Some substitution functions *)

    (* [firstVar]: Add this to all indices of variables appearing within [e].
     * [firstFree] tells us which is the first regular variable to be treated as a unification variable. *)
    Fixpoint substExpr (firstVar firstFree : nat) (s : U.Subst types) (e : expr types) : expr types :=
      match e with
        | Expr.Const _ _ => e
        | Var x => if lt_dec x firstFree
          then Var (x + firstVar)
          else match U.Subst_lookup (x - firstFree) s with
                 | None => e
                 | Some e' => e'
               end
        | UVar _ => e
        | Expr.Func f es => Expr.Func f (map (substExpr firstVar firstFree s) es)
        | Equal t e1 e2 => Equal t (substExpr firstVar firstFree s e1) (substExpr firstVar firstFree s e2)
        | Not e1 => Not (substExpr firstVar firstFree s e1)
      end.

    Definition substSheap (firstVar firstFree : nat) (s : U.Subst types) (sh : SHeap types pcType stateType)
      : SHeap types pcType stateType :=
      {| impures := MM.mmap_map (map (substExpr firstVar firstFree s)) (impures sh)
       ; pures := map (substExpr firstVar firstFree s) (pures sh)
       ; other := other sh
       |}.


    Fixpoint substExprBw (offset firstFree : nat) (s : U.Subst types) (e : expr types) : expr types :=
      match e with
        | Expr.Const _ _ => e
        | Var x => if lt_dec x firstFree
          then e
          else match U.Subst_lookup (x - firstFree + offset) s with
                 | None => e
                 | Some e' => e'
               end
        | UVar _ => e
        | Expr.Func f es => Expr.Func f (map (substExprBw offset firstFree s) es)
        | Equal t e1 e2 => Equal t (substExprBw offset firstFree s e1) (substExprBw offset firstFree s e2)
        | Not e1 => Not (substExprBw offset firstFree s e1)
      end.

    Fixpoint substExprBw' (offset firstFree : nat) (s : U.Subst types) (e : expr types) : expr types :=
      match e with
        | Expr.Const _ _ => e
        | Var x => if lt_dec x firstFree
          then UVar (x + offset)
          else match U.Subst_lookup (x - firstFree + offset) s with
                 | None => e
                 | Some e' => e'
               end
        | UVar _ => e
        | Expr.Func f es => Expr.Func f (map (substExprBw' offset firstFree s) es)
        | Equal t e1 e2 => Equal t (substExprBw' offset firstFree s e1) (substExprBw' offset firstFree s e2)
        | Not e1 => Not (substExprBw' offset firstFree s e1)
      end.

    Definition substSheapBw (offset firstFree : nat) (s : U.Subst types) (sh : SHeap types pcType stateType) 
      : SHeap types pcType stateType :=
      {| impures := MM.mmap_map (map (substExprBw' offset firstFree s)) (impures sh)
       ; pures := map (substExprBw' offset firstFree s) (pures sh)
       ; other := other sh
       |}.


    (** The type of one unfolding lemma *)
    Record lemma := {
      Foralls : variables;
      (* The lemma statement begins with this sequence of [forall] quantifiers over these types. *)
      Hyps : list (expr types);
      (* Next, we have this sequence of pure hypotheses. *)
      Lhs : sexpr types pcType stateType;
      Rhs : sexpr types pcType stateType
      (* Finally, we have this separation implication, with lefthand and righthand sides. *)
    }.

    Definition WellTyped_lemma tfuncs tpreds (l : lemma) : bool :=
      allb (fun x => is_well_typed tfuncs nil (Foralls l) x tvProp) (Hyps l) &&
      WellTyped_sexpr tfuncs tpreds nil (Foralls l) (Lhs l) && 
      WellTyped_sexpr tfuncs tpreds nil (Foralls l) (Rhs l).

    (** Helper function to add a sequence of implications in front of a [Prop] *)
    Definition hypD (H : expr types) (meta_env var_env : env types) : Prop :=
      match exprD funcs meta_env var_env H tvProp with
        | None => False
        | Some P => P
      end.

    Fixpoint implyEach (Hs : list (expr types)) (meta_env var_env : env types) (P : Prop) : Prop :=
      match Hs with
        | nil => P
        | H :: Hs' => hypD H meta_env var_env -> implyEach Hs' meta_env var_env P
      end.

    (** The meaning of a lemma statement *)

    (* Redefine to use the opposite quantifier order *)
    Fixpoint forallEachR (ls : variables) : (env types -> Prop) -> Prop :=
      match ls with
        | nil => fun cc => cc nil
        | a :: b => fun cc =>
          forallEachR b (fun r => forall x : tvarD types a, cc (existT _ a x :: r))
      end.

    Definition lemmaD (meta_base var_base : env types) (lem : lemma) : Prop :=
      WellTyped_lemma (typeof_funcs funcs) (Predicates_typeof preds) lem = true /\
      forallEachR (Foralls lem) (fun env =>
        implyEach (Hyps lem) meta_base (env ++ var_base)
        (forall specs, himp funcs preds meta_base (env ++ var_base) specs (Lhs lem) (Rhs lem))).

    (** Preprocessed databases of hints *)

    Definition hintSide := list lemma.
    (* A complete set of unfolding hints of a single sidedness (see below) *)

    Definition hintSideD := Forall (lemmaD nil nil).

    Record hintsPayload := {
      Forward : hintSide;
      (* Apply on the lefthand side of an implication *)
      Backward : hintSide 
      (* Apply on the righthand side *)
    }.

    Definition default_hintsPayload : hintsPayload := 
    {| Forward := nil
     ; Backward := nil
     |}.

    Definition composite_hintsPayload (l r : hintsPayload) : hintsPayload :=
      {| Forward := Forward l ++ Forward r
       ; Backward := Backward l ++ Backward r
       |}.

    Record hintsSoundness (Payload : hintsPayload) : Prop := {
      ForwardOk : hintSideD (Forward Payload);
      BackwardOk : hintSideD (Backward Payload)
    }.
    
    Theorem hintsSoundness_default : hintsSoundness default_hintsPayload.
    Proof.
      econstructor; constructor.
    Qed.
    
    Theorem hintsSoundness_composite l r (L : hintsSoundness l) (R : hintsSoundness r) 
      : hintsSoundness (composite_hintsPayload l r).
    Proof.
      econstructor; simpl; eapply Folds.Forall_app; solve [ eapply ForwardOk; auto | eapply BackwardOk; auto ].
    Qed.

    (** Applying up to a single hint to a hashed separation formula *)

    Fixpoint find A B (f : A -> option B) (ls : list A) : option B :=
      match ls with
        | nil => None
        | x :: ls' => match f x with
                        | None => find f ls'
                        | v => v
                      end
      end.

    Lemma findOk : forall A B (f : A -> option B) ls res,
      find f ls = Some res ->
      exists a, In a ls /\ f a = Some res.
    Proof.
      clear. induction ls; intros; simpl in *; try congruence.
      revert H. consider (f a); intros. inversion H0; subst; exists a; intuition.
      eapply IHls in H0. destruct H0; intuition. eauto.
    Qed.

    Fixpoint findWithRest' A B (f : A -> list A -> option B) (ls acc : list A) : option B :=
      match ls with
        | nil => None
        | x :: ls' => match f x (rev_append acc ls') with
                        | None => findWithRest' f ls' (x :: acc)
                        | v => v
                      end
      end.

    Lemma findWithRest'Ok : forall A B (f : A -> list A -> option B) ls acc res,
      findWithRest' f ls acc = Some res ->
      exists xs x xs', ls = xs ++ x :: xs' /\ f x (rev acc ++ xs ++ xs') = Some res.
    Proof.
      clear.
      induction ls; intros; simpl in *; try congruence.
      revert H; consider (f a (rev_append acc ls)); intros.
      inversion H0; clear H0; subst. exists nil. exists a. exists ls. simpl. rewrite rev_append_rev in H; auto.
      eapply IHls in H0. do 3 destruct H0. intuition. subst. clear H. simpl in *. rewrite app_ass in H2. simpl in *.
      exists (a :: x). simpl. exists x0. exists x1. intuition.
    Qed.

    Definition findWithRest A B (f : A -> list A -> option B) (ls : list A) : option B :=
      findWithRest' f ls nil.

    Lemma findWithRestOk : forall A B (f : A -> list A -> option B) ls res,
      findWithRest f ls = Some res ->
      exists xs x xs', ls = xs ++ x :: xs' /\ f x (xs ++ xs') = Some res.
    Proof.
      clear. unfold findWithRest; simpl. intros. eapply findWithRest'Ok in H. eauto.
    Qed.

    (* As we iterate through unfolding, we modify this sort of state. *)
    Record unfoldingState := {
      Vars : variables;
      UVars : variables;
      Heap : SH.SHeap types pcType stateType
    }.

    Section unfoldOne.
      Variable unify_bound : nat.
      
      Variable prover : ProverT types.
      (* This prover must discharge all pure obligations of an unfolding lemma, if it is to be applied. *)
      Variable facts : Facts prover.

      Variable hs : hintSide.
      (* Use these hints to unfold impure predicates. *)

      Fixpoint Subst_to_env U G (s : U.Subst types) (ts : variables) (cur : uvar) : option (env types) :=
        match ts with
          | nil => Some nil 
          | t :: ts =>
            match U.Subst_lookup cur s with
              | None => None 
              | Some e => 
                match Subst_to_env U G s ts (S cur) with
                  | None => None
                  | Some env =>
                    match exprD funcs U G e t with
                      | None => None
                      | Some v => Some (@existT _ _ t v :: env)
                    end
                end
            end
        end.

      Lemma forallEachR_sem : forall vs P,
        forallEachR vs P <-> (forall e, map (@projT1 _ _) e = vs -> P e).
      Proof.
        clear. split; revert P; induction vs; simpl; intros.
          destruct e; simpl in *; try congruence.
          destruct e; simpl in *; try congruence. inversion H0; clear H0; subst. eapply IHvs in H; eauto.
            destruct s; eapply H.
          eapply H; reflexivity.
          eapply IHvs; intros. eapply H. simpl. f_equal; auto.
      Qed.

      Lemma Subst_to_env_env : forall U G S' TS cur e0,
        Subst_to_env U G S' TS cur = Some e0 ->
        map (@projT1 _ _) e0 = TS.
      Proof.
        induction TS; simpl; intros;
          repeat match goal with
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                   | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
                     revert H ; case_eq X ; intros; try congruence
                   | [ |- _ ] => progress ( simpl in * )
                   | [ |- _ ] => progress subst
                 end; try solve [ intuition ].
        f_equal. eauto.
      Qed.


      Theorem unify_args_forallEachR : forall tfuncs tU tG U G l r D (S : U.Subst types) S' P env cur TS,
        U.Subst_WellTyped tfuncs tU tG S ->
        all2 (@is_well_typed _ tfuncs tU tG) l D = true ->
        all2 (@is_well_typed _ tfuncs tU tG) r D = true ->
        fold_left_2_opt (U.exprUnify unify_bound) l r S = Some S' ->
        Subst_to_env U G S' TS cur = Some env ->
        forallEachR TS P ->
        P env.
      Proof.
        clear.
        induction l; destruct TS; try congruence; simpl in *; intros;
          repeat match goal with
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                   | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
                     revert H ; case_eq X ; intros; try congruence
                   | [ |- _ ] => progress ( simpl in * )
                   | [ |- _ ] => progress subst
                   | [ H : U.exprUnify _ _ _ _ = Some _ |- _ ] => 
                     generalize H ; generalize H; 
                     apply U.exprUnify_Extends in H ;
                     let H := fresh "H" in
                     intro H ;
                     apply U.exprUnify_sound in H
                 end; try solve [ intuition ].
        eapply forallEachR_sem in H4. eapply H4.
        eauto using Subst_to_env_env.        
        
        intro. eapply IHl in H4. eapply H4. 4: eauto. eauto using U.exprUnify_WellTyped. eauto. eauto. eauto.
      Qed.

(*
      Parameter exprSubstU_spec : forall e a b c e',
        exprSubstU a b c e = e' ->
        forall A B C D t v,
          length B = a ->
          length B + length C = b ->
          length A = c ->
          exprD funcs A (B ++ C ++ D) e t = Some v ->
          exprD funcs (A ++ C) (B ++ D) e' t = Some v.
*)

      Fixpoint checkAllInstantiated (from : nat) (ts : variables) (sub : U.Subst types) : bool :=
        match ts with
          | nil => true
          | _ :: ts => if U.Subst_lookup from sub then checkAllInstantiated (S from) ts sub else false
        end.


      (** Determine if a lemma is applicable.
       ** - [firstUVar] an index larger than the largest unification variable
       ** - [lem] is the lemma to apply
       ** - [args] is the outside
       ** - [key] is the patterns (closed by [Foralls lem]) that need to unify with [args])
       **)
      Definition applicable (firstUvar : nat) (lem : lemma) (args key : exprs types) : option (U.Subst types) :=
        let numForalls := length (Foralls lem) in
        match fold_left_2_opt (U.exprUnify unify_bound) args (map (exprSubstU 0 numForalls firstUvar) key) (U.Subst_empty _) with
          | None => None
          | Some subst =>
            (* Now we must make sure all of the lemma's pure obligations are provable. *)
            if allb (Prove prover facts) (map (substExpr firstUvar O subst) (Hyps lem))
            then if EqNat.beq_nat (U.Subst_size subst) numForalls && checkAllInstantiated 0 (Foralls lem) subst
                 then Some subst
                 else None
            else None
        end.

(*
      Lemma checkAllInstantiated_lookup : forall sub ts from,
        checkAllInstantiated from ts sub = true ->
        forall tfuncs tU tG,
          from = length tU ->
          U.Subst_WellTyped tfuncs (tU ++ ts) tG sub ->
          forall n t, 
            nth_error ts n = Some t ->
            exists e,
            U.Subst_lookup (from + n) sub = Some e /\
            is_well_typed tfuncs tU tG e t = true.
      Proof.
        induction ts using rev_ind; intros.
          destruct n; simpl in *; unfold error in *; congruence.

          
(*
        induction ts; simpl; intros. 

        
          consider (U.Subst_lookup from sub); intros. specialize (IHts _ H3 tfuncs (tU ++ a :: nil) tG).
          rewrite app_length in IHts. simpl length in IHts. rewrite plus_comm in IHts.
          rewrite app_ass in IHts. simpl app in IHts. subst; specialize (IHts refl_equal H1).
          destruct n; simpl in *. inversion H2; clear H2; subst. rewrite plus_0_r. eexists; split; eauto.
          { admit. }
          { eapply IHts in H2. destruct H2. intuition. clear IHts. rewrite plus_comm. simpl. rewrite plus_comm.
            eexists; split; eauto.
 
          destruct n; simpl in *. inversion H4; clear H4; subst. rewrite plus_0_r in H3.


inversion H3; clear H3; subst.
          s
*)
      Admitted.
*)

      Lemma checkAllInstantiated_Subst_to_env_success : forall sub ts from,
        checkAllInstantiated from ts sub = true ->
        forall U G tfuncs tU tG,
          WellTyped_env tU U ->
          WellTyped_env tG G ->
          WellTyped_funcs tfuncs funcs ->
          from = length tU ->
          U.Subst_WellTyped tfuncs (tU ++ ts) tG sub ->
          exists env, Subst_to_env U G sub ts from = Some env.
      Proof.
      Admitted.

      Lemma is_well_typed_weaken : forall tf tU tG e t,
        is_well_typed (types := types) tf tU tG e t = true ->
        forall u g,
          is_well_typed tf (tU ++ u) (tG ++ g) e t = true.
      Proof.
        induction e; simpl; intros; 
          repeat match goal with
                   | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
                     consider X; intros
                   | [ H : _ === _ |- _ ] => unfold equiv in H; subst
                   | [ H : _ && _ = _ |- _ ] => apply andb_true_iff in H; destruct H
                   | [ H : _ |- _ ] => rewrite H by auto
                   | [ |- _ ] => erewrite nth_error_weaken by eauto
                   | [ |- _ ] => rewrite EquivDec_refl_left
                 end; auto.
        destruct t0. simpl in *. revert H1. generalize TDomain. induction H; destruct TDomain0; intros; simpl in *; auto.
        consider (is_well_typed tf tU tG x t); intros. erewrite H by eauto. eauto.
      Qed.


      Lemma all2_is_well_typed_weaken : forall tf tU tG es ts,
        all2 (is_well_typed (types := types) tf tU tG) es ts = true ->
        forall u g,
          all2 (is_well_typed tf (tU ++ u) (tG ++ g)) es ts = true.
      Proof.
        clear. intros. eapply all2_impl; eauto using is_well_typed_weaken.
      Qed.

      Lemma exprSubstU_WellTyped : forall tf tU tG ext (a : expr types) t,
        is_well_typed tf tU (tG ++ ext) a t = true ->
        is_well_typed tf (tU ++ ext) tG (exprSubstU (length tG) (length tG + length ext) (length tU) a) t = true.
      Proof.
        clear. induction a; simpl; intros; 
        repeat match goal with
                 | [ H : match ?X with tvProp => _ | tvType _ => _ end = _ |- _ ] =>
                   destruct X; try congruence
                 | [ H : (_ && _) = true |- _ ] => apply andb_true_iff in H; destruct H
                 | [ H : _ |- _ ] => rewrite H by auto
                 | [ |- context [ if NPeano.ltb ?A ?B then _ else _ ] ] =>
                   consider (NPeano.ltb A B); intros
                 | [ |- _ ] => 
                   rewrite nth_error_app_L by omega
                 | [ |- _ ] => rewrite nth_error_app_R by omega
                 | [ H : _ |- _ ] => 
                   rewrite nth_error_app_R in H by omega 
                 | [ H : _ |- _ ] => 
                   rewrite nth_error_app_L in H by omega 
                 | [ |- _ ] => progress ( simpl in * )
                 | [ H : match nth_error _ ?X with _ => _ end = _ |- match nth_error _ ?Y with _ => _ end = _ ] => 
                   cutrewrite (Y = X); [ auto | omega ] 
               end; auto.
        exfalso. admit.
        consider (nth_error tU x); intros. erewrite nth_error_weaken by eauto. auto.
        consider (nth_error tf f); intros. consider (equiv_dec t (TRange t0)); intros.
        unfold equiv in *; simpl in *; subst. admit.
      Qed.
     
      Lemma typeof_env_length : forall g, 
        length (typeof_env (types := types) g) = length g.
      Proof.
        clear. apply map_length.
      Qed.
      Lemma implyEach_instantiate : forall HYPS U G,
        AllProvable funcs U G HYPS ->
        forall cc,
          implyEach HYPS U G cc ->
          cc.
      Proof.
        induction HYPS; simpl; intros; auto;
          repeat match goal with
                   | [ H : _ /\ _ |- _ ] => destruct H
                   | [ H : _ && _ = _ |- _ ] => 
                     apply andb_true_iff in H; destruct H
                 end.
        eapply IHHYPS; eauto.
      Qed. 

      (* Returns [None] if no unfolding opportunities are found.
       * Otherwise, return state after one unfolding. *)
      Definition unfoldForward (s : unfoldingState) : option unfoldingState :=
        let imps := SH.impures (Heap s) in
        let firstUvar  := length (UVars s) in
        let firstVar   := length (Vars s) in
        find (fun h =>
          match Lhs h with
            | Func f args' => 
              match FM.find f imps with
                | None => None
                | Some argss =>
                  let numForalls := length (Foralls h) in
                  findWithRest (fun args argss =>
                    (* We must tweak the arguments by substituting unification variables for 
                     * [forall]-quantified variables from the lemma statement. *)
                    match applicable firstUvar h args args' with
                      | None => None 
                      | Some subs =>
(*
                    let args' := map (exprSubstU O numForalls firstUvar) args' in

                    (* Unify the respective function arguments. *)
                    match fold_left_2_opt (U.exprUnify unify_bound) args' args (U.Subst_empty _) with
                      | None => None
                      | Some subs =>
                        (* Now we must make sure all of the lemma's pure obligations are provable. *)
                        if allb (Prove prover facts) (map (substExpr firstUvar O subs) (Hyps h)) then
                          (* Remove the current call from the state, as we are about to replace
                           * it with a simplified set of pieces. *)
*)
                          let impures' := FM.add f argss (impures (Heap s)) in
                          let sh := {| impures := impures';
                            pures := pures (Heap s);
                            other := other (Heap s) |} in

                          (* Time to hash the hint RHS, to (among other things) get the new existential variables it creates. *)
                          let (exs, sh') := hash (Rhs h) in

                          (* Apply the substitution that unification gave us. *)
                          let sh' := substSheap firstVar (length exs) subs sh' in

                          (* The final result is obtained by joining the hint RHS with the original symbolic heap. *)
                          Some {| Vars := Vars s ++ rev exs
                                ; UVars := UVars s
                                ; Heap := star_SHeap sh sh'
                                |}
(*
                        else
                          None
*)
                    end                    
                  ) argss
              end
            | _ => None
          end) hs.
     
      Definition unfoldBackward (s : unfoldingState) : option unfoldingState :=
        let imps := SH.impures (Heap s) in
        let firstUvar := length (UVars s) in
        find (fun h =>
          match Rhs h with
            | Func f args' =>
              match FM.find f imps with
                | None => None
                | Some argss => 
                  findWithRest (fun args argss =>
                    let args' := map (exprSubstU O (length (Foralls h)) firstUvar) args' in

                    (* Unify the respective function arguments. *)
                    match fold_left_2_opt (U.exprUnify unify_bound) args' args (U.Subst_empty _) with
                      | None => None
                      | Some subs =>
                        (* Now we must make sure all of the lemma's pure obligations are provable. *)
                        if allb (Prove prover facts) (map (substExprBw firstUvar O subs) (Hyps h)) then
                          (* Remove the current call from the state, as we are about to replace it with a 
                           * simplified set of pieces. *)
                          let impures' := FM.add f argss (impures (Heap s)) in
                          let sh := {| impures := impures'
                                     ; pures := pures (Heap s)
                                     ; other := other (Heap s) |} in

                          (* Time to hash the hint LHS, to (among other things) get the new existential variables it creates. *)
                          let (exs, sh') := hash (Lhs h) in

                          (* Newly introduced variables must be replaced with unification variables, and 
                           * universally quantified variables must be substituted for. *)
                          let sh' := substSheapBw firstUvar (length exs) subs sh' in

                          (* The final result is obtained by joining the hint LHS with the original symbolic heap. *)
                          Some {| Vars := Vars s
                                ; UVars := UVars s ++ rev exs
                                ; Heap := star_SHeap sh sh'
                                |}
                        else
                          None
                    end
                  ) argss
              end
            | _ => None
          end) hs.

    End unfoldOne.

    Section unfolder.
      Definition unify_bound := 5.
      Variable hs : hintsPayload.
      Variable prover : ProverT types.

      (* Perform up to [bound] simplifications, based on [hs]. *)
      Fixpoint forward (bound : nat) (facts : Facts prover) (s : unfoldingState) : unfoldingState :=
        match bound with
          | O => s
          | S bound' =>
            match unfoldForward unify_bound prover facts (Forward hs) s with
              | None => s
              | Some s' => forward bound' facts s'
            end
        end.

      Fixpoint backward (bound : nat) (facts : Facts prover) (s : unfoldingState) : unfoldingState :=
        match bound with
          | O => s
          | S bound' =>
            match unfoldBackward unify_bound prover facts (Backward hs) s with
              | None => s
              | Some s' => backward bound' facts s'
            end
        end.

      Hypothesis hsOk : hintsSoundness hs.
      Hypothesis PC : ProverT_correct prover funcs.

      Check applicable.

      Theorem applicableOk : forall facts U G lem args args' sub TS,
        lemmaD nil nil lem ->
        all2 (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G)) args TS = true ->
        all2 (is_well_typed (typeof_funcs funcs) nil (Foralls lem)) args' TS = true ->
        applicable unify_bound prover facts (length U) lem args args' = Some sub ->
        map (U.exprInstantiate sub) args = map (U.exprInstantiate sub) args' /\
        AllProvable funcs U G (map (U.exprInstantiate sub) (Hyps lem)).
      Proof.
        unfold applicable; intros.
        repeat match goal with
                 | [ H : match ?X with _ => _ end = _ |- _ ] => 
                   consider X; try congruence; intros
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               end.
        eapply all2_is_well_typed_weaken with (u := Foralls lem) (g := nil) in H0. apply andb_true_iff in H4. destruct H4.

        cut (U.Subst_WellTyped (typeof_funcs funcs) (typeof_env U ++ Foralls lem) (typeof_env G) sub); intros.
        { eapply checkAllInstantiated_Subst_to_env_success in H5 (*; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.*). 5: eauto. 2: eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs. 2: eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs. 2: eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs. destruct H5.
          destruct H.
          eapply unify_args_forallEachR in H2; eauto using U.Subst_empty_WellTyped.
          Focus 2.

          rewrite all2_map_1.
          eapply all2_impl. eauto. clear. intros. rewrite <- app_nil_l with (l := Foralls lem) in H.
          eapply is_well_typed_weaken with (u := typeof_env U) (g := nil) in H. rewrite app_nil_r in H.
          eapply exprSubstU_WellTyped in H. simpl in *. eapply is_well_typed_weaken with (g := typeof_env G) (u := nil) in H.
          repeat rewrite app_nil_r in *. simpl in *.

          rewrite typeof_env_length in H. eassumption.
          simpl in *.


(*
eapply H2. unfold hypD. unfold Provable in H.

consider (exprD funcs nil x a tvProp); intros.
            admit. 
            Lemma Subst_to_env_typeof_env : forall U G sub TS cur x,
              Subst_to_env U G sub TS cur = Some x ->
              typeof_env x = TS.
            Proof.
              induction TS; simpl; intros; 
                repeat match goal with
                         | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                         | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
                           consider X; intros
                         | [ |- _ ] => progress ( simpl in * )
                         | [ |- _ ] => f_equal ; [] 
                       end; eauto; try congruence.
            Qed.
            eapply Subst_to_env_typeof_env in H. subst.
            eapply is_well_typed_correct in H1; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
            2: instantiate (1 := nil); reflexivity.
            destruct H1; congruence.
          Qed.
*)
          eapply implyEach_instantiate in H2. 
          
        

      Admitted.



      Lemma app_len_2 : forall T (a b c d : list T),
        a ++ b = c ++ d ->
        length b = length d ->
        a = c /\ b = d.
      Proof.
        clear. induction a; destruct c; simpl; intuition; subst; auto;
        simpl in *; try rewrite app_length in H0; 
          try solve [ try generalize dependent (length d); intros; exfalso; omega ].
        inversion H. subst. f_equal. eapply IHa in H3; eauto. intuition.
        inversion H. eapply IHa in H3; intuition.
      Qed.

      Lemma ST_himp_heq_L : forall cs U G P Q S,
        heq funcs preds U G cs P Q ->
        ST.himp cs (sexprD funcs preds U G Q) S ->
        ST.himp cs (sexprD funcs preds U G P) S. 
      Proof.
        clear. intros. rewrite H. auto.
      Qed.

      Lemma Equal_remove_add_remove : forall T k (v : T) m,
        FM.Equal (FM.remove k (FM.add k v m)) (FM.remove k m).
      Proof.
        clear. intros. red. intros.
        repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
        consider (MF.FACTS.eq_dec k y); auto.
      Qed.

      Lemma unfoldForward_vars : forall unify_bound facts P Q,
        unfoldForward unify_bound prover facts (Forward hs) P = Some Q ->
        exists vars_ext, Vars Q = Vars P ++ vars_ext /\ UVars Q = UVars P.
      Proof.
        unfold unfoldForward. intros.
        repeat match goal with
                 | [ H : _ = Some _ |- _ ] => eapply findOk in H || eapply findWithRestOk in H
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
                   (revert H; consider X; intros; try congruence) ; []                                           
               end; simpl. eexists; intuition.
      Qed.

      Opaque ST_EXT.existsEach.

      Lemma unfoldForwardOk : forall unify_bound meta_env vars_env cs facts P Q,
        Valid PC meta_env vars_env facts ->
        unfoldForward unify_bound prover facts (Forward hs) P = Some Q ->
        ST.himp cs
        (sexprD funcs preds meta_env vars_env (sheapD (Heap P)))
        (ST_EXT.existsEach (skipn (length vars_env) (Vars Q))
          (fun vars_ext : list {t : tvar & tvarD types t} =>
            sexprD funcs preds meta_env (vars_env ++ vars_ext) (sheapD (Heap Q)))).
      Proof.
        unfold unfoldForward. intros.
        repeat match goal with
                 | [ H : _ = Some _ |- _ ] => eapply findOk in H || eapply findWithRestOk in H
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
                   (revert H; consider X; intros; try congruence) ; []                                           
               end.
        destruct P; simpl in *.

        destruct Heap0; simpl in *.
        eapply ST_himp_heq_L with (Q := Star (SH.sheapD {| impures := FM.add f (x0 ++ x2) impures0
          ; pures := pures0
          ; other := other0
        |})
        (Func f x1)).
        { repeat rewrite SH.sheapD_def. simpl.
          rewrite SH.impuresD_Add with (f := f) (argss := x0 ++ x1 :: x2) (i := FM.remove f impures0).
          rewrite SH.impuresD_Add with (f := f) (argss := x0 ++ x2) (i := FM.remove f (FM.add f (x0 ++ x2) impures0))
            (i' := FM.add f (x0 ++ x2) impures0). heq_canceler.
          symmetry. rewrite impuresD_Equiv.
          2: rewrite Equal_remove_add_remove; reflexivity. reflexivity.
          clear. red; intros. repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
          destruct (MF.FACTS.eq_dec f y); reflexivity. intro. apply MM.FACTS.remove_in_iff in H3. intuition congruence.
          red. intros. repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o). consider (MF.FACTS.eq_dec f y); subst; auto. 
          intro. apply MM.FACTS.remove_in_iff in H3. intuition congruence. }

        Lemma hintSideD_In : forall hs,
          hintSideD hs -> forall x, In x hs -> lemmaD nil nil x.
        Proof.
          clear. induction 1. inversion 1.
          intros. inversion H1; subst; auto.
        Qed.
        
          eapply hintSideD_In in H0; eauto using ForwardOk.
(*
          eapply unify_args_forallEachR in H4. 6: eapply H0. simpl in *.
          SearchAbout fold_left_2_opt.
*)
        
      Admitted.

      Lemma skipn_length_gt : forall T (ls : list T) n,
        length ls <= n ->
        skipn n ls = nil.
      Proof.
        clear. induction ls; destruct n; simpl; intuition; auto.
      Qed.

      Lemma skipn_length_all : forall T U (F : T -> U) ls ls',
        map F ls = ls' ->
        skipn (length ls) ls' = nil.
      Proof.
        clear; intros. eapply skipn_length_gt. rewrite <- H. rewrite map_length. omega.
      Qed.

      Hint Resolve skipn_length_all : list_length.
      Hint Rewrite skipn_length_all using (eauto with list_length) : list_length.
      
      Lemma forwardLength : forall bound facts P Q,
        forward bound facts P = Q ->
        exists vars_ext (* meta_ext *),
          Vars Q = Vars P ++ vars_ext /\
          UVars Q = UVars P (* ++ meta_ext *).
      Proof.
        clear. induction bound; intros; simpl in *; eauto.
          subst; exists nil; repeat rewrite app_nil_r; auto.
          consider (unfoldForward unify_bound prover facts (Forward hs) P); intros.
          { eapply IHbound in H0. eapply unfoldForward_vars in H.
            repeat match goal with
                     | [ H : exists x, _ |- _ ] => destruct H
                     | [ H : _ /\ _ |- _ ] => destruct H
                     | [ H : _ = _ |- _ ] => rewrite H
                   end. repeat rewrite app_ass. eauto. }
          { subst. exists nil; repeat rewrite app_nil_r; eauto. }
      Qed.

      Lemma rw_skipn_app : forall T (ls ls' : list T) n,
        length ls = n ->
        skipn n (ls ++ ls') = ls'.
      Proof.
        clear. induction ls; destruct n; simpl in *; intros; auto; congruence. 
      Qed.
      Lemma length_equal_map_rev : forall T U (F : T -> U) ls ls',
        map F ls' = rev ls ->
        length ls = length ls'.
      Proof.
        clear. intros. rewrite <- rev_length. rewrite <- H. rewrite map_length. auto.
      Qed.
      Hint Resolve length_equal_map_rev : list_length.
      Lemma eq_proves_gt : forall a b,
        a = b -> a <= b.
      Proof.
        clear. intros; omega.
      Qed.
      Lemma map_length_hint : forall T U (F : T -> U) a b,
        map F a = b -> length b = length a.
      Proof.
        clear. intros. subst. rewrite map_length. auto.
      Qed.
      Hint Resolve eq_proves_gt map_length_hint skipn_length_gt : list_length.

      Theorem forwardOk : forall cs bound facts P Q,
        forward bound facts P = Q ->
        forall meta_env vars_env,
        map (@projT1 _ _) meta_env = P.(UVars) -> (** meta_env instantiates the uvars **)
        map (@projT1 _ _) vars_env = P.(Vars) ->
        Valid PC meta_env vars_env facts ->
        ST.himp cs (sexprD funcs preds meta_env vars_env (sheapD (Heap P)))
                   (ST_EXT.existsEach (skipn (length vars_env) Q.(Vars)) (fun vars_ext : list { t : tvar & tvarD types t } =>
                     (sexprD funcs preds meta_env (vars_env ++ vars_ext) (sheapD (Heap Q))))).
      Proof.
        induction bound; simpl; intros.
        { subst; repeat split; try reflexivity.
          cutrewrite (skipn (length vars_env) (Vars Q) = nil).
          rewrite ST_EXT.existsEach_nil. rewrite app_nil_r. reflexivity.
          eauto with list_length. }
        { revert H; case_eq (unfoldForward unify_bound prover facts (Forward hs) P); intros.
          { subst. generalize H. eapply unfoldForwardOk with (cs := cs) in H; eauto. rewrite H.
            intros. eapply unfoldForward_vars in H3. do 2 destruct H3. intuition. 
            remember (forward bound facts u). symmetry in Hequ0.
            specialize (IHbound _ _ _ Hequ0).
            eapply forwardLength in Hequ0.
            repeat match goal with
                     | [ H : _ = _ |- _ ] => rewrite H
                     | [ H : exists x, _ |- _ ] => destruct H
                     | [ H : _ /\ _ |- _ ] => destruct H
                     | [ |- _ ] => rewrite app_ass in *
                     | [ |- _ ] => rewrite rw_skipn_app by eauto with list_length
                   end.
            erewrite <- app_nil_r with (l := x) at 1.
            eapply ST.existsEach_app; intros. simpl.
            rewrite IHbound; eauto with list_length.
            rewrite H5. repeat (rewrite app_nil_r || rewrite app_ass). 
            rewrite rw_skipn_app. eapply ST_exs_env_same; intros. 
            repeat (rewrite app_nil_r || rewrite app_ass). reflexivity.

            rewrite H3. repeat rewrite app_length. subst. rewrite <- H1. repeat rewrite map_length. reflexivity.
 
            rewrite H4; auto.
            
            rewrite map_app.
            repeat match goal with
                     | [ H : _ = _ |- _ ] => rewrite H
                   end. rewrite app_nil_r.
            f_equal; auto. 
            rewrite <- app_nil_r with (l := meta_env); eapply Valid_weaken; eauto. }
          { subst. erewrite skipn_length_all by eauto with list_length. simpl. rewrite app_nil_r. reflexivity. } }
      Qed.

      Theorem backwardOk : forall cs bound facts P Q meta_env vars_env,
        backward bound facts P = Q ->
        map (@projT1 _ _) meta_env = P.(UVars) -> (** meta_env instantiates the uvars **)
        map (@projT1 _ _) vars_env = rev P.(Vars) ->
        Valid PC meta_env vars_env facts ->
        ST.himp cs (ST_exs_env (skipn (length meta_env) Q.(UVars)) (fun meta_ext : list { t : tvar & tvarD types t } => 
                      (sexprD funcs preds (meta_env ++ meta_ext) vars_env (sheapD (Heap Q)))))
                   (sexprD funcs preds meta_env vars_env (sheapD (Heap P))).
      Proof.
        induction bound; simpl; intros.
        { subst. cutrewrite (skipn (length meta_env) (UVars Q) = nil). simpl. rewrite app_nil_r. reflexivity.
          erewrite <- map_length. instantiate (1 := @projT1 _ _). rewrite H0. admit.
        }
        { revert H. admit.
        }
      Qed.

(*
      (* This soundness statement is clearly unsound, but I'll start with it to enable testing. *)
      (** TODO: Break this into two lemmas, one for forward and one for backward **)
      Theorem unfolderOk : forall bound P Q,
        (let (exsP, shP) := hash P in
         let (exsQ, shQ) := hash Q in
         let summ := Summarize prover (pures shP) in
         let sP := forward bound summ {| Vars := exsP;
           UVars := nil;
           Heap := shP |} in
         let shQ := sheapSubstU O (length exsQ) O shQ in
         let sQ := backward bound summ {| Vars := Vars sP;
           UVars := exsQ;
           Heap := shQ |} in
         forallEach (Vars sP) (fun alls =>
           exists_subst funcs nil alls (env_of_Subst (empty_Subst _) (UVars sQ) 0) (fun exsQ =>
             forall cs, ST.himp cs (sexprD funcs preds nil alls (sheapD (Heap sP)))
               (sexprD funcs preds exsQ nil (sheapD (Heap sQ))))))
        -> forall cs, ST.himp cs (sexprD funcs preds nil nil P) (sexprD funcs preds nil nil Q).
      Proof.
        generalize hsOk. generalize PC. admit.
      Qed.
*)
    End unfolder.
  End env.

(*
  Ltac unfold_unfolder H :=
    match H with
      | tt => 
        cbv beta iota zeta delta [ 
          Hints Foralls Hints Hyps Lhs Rhs 
          Forward Backward 
          forward backward 
          unfoldForward unfoldBackward
*)


  (** * Reflecting hints *)
  Require Reflect.
  Module SEP_REIFY := SepExpr.ReifySepExpr SE.

  (* This tactic processes the part of a lemma statement after the quantifiers. *)
  Ltac collectTypes_hint' isConst P types k :=
    match P with
      | fun x => @?H x -> @?P x =>
        let types := ReifyExpr.collectTypes_expr ltac:(isConst) H types in
          collectTypes_hint' ltac:(isConst) P types k
      | fun x => forall cs, @ST.himp ?pcT ?stT cs (@?L x) (@?R x) =>
        SEP_REIFY.collectTypes_sexpr ltac:(isConst) L types ltac:(fun types =>
          SEP_REIFY.collectTypes_sexpr ltac:(isConst) R types k)
      | fun x => _ (@?L x) (@?R x) =>
        SEP_REIFY.collectTypes_sexpr ltac:(isConst) L types ltac:(fun types =>
          SEP_REIFY.collectTypes_sexpr ltac:(isConst) R types k)
    end.

  (* This tactic adds quantifier processing. *)
  Ltac collectTypes_hint isConst P types k :=
    match P with
      | fun xs : ?T => forall x : ?T', @?f xs x =>
        match T' with
          | PropX.codeSpec _ _ => fail 1
          | _ => match type of T' with
                   | Prop => fail 1
                   | _ => let P := eval simpl in (fun x : ReifyExpr.VarType (T * T') =>
                     f (@ReifyExpr.openUp _ T (@fst _ _) x) (@ReifyExpr.openUp _ T' (@snd _ _) x)) in
                   let types := Reflect.cons_uniq T' types in
                     collectTypes_hint ltac:(isConst) P types k
                 end
        end
      | _ => collectTypes_hint' ltac:(isConst) P types k
    end.

  (* Finally, this tactic adds a loop over all hints. *)
  Ltac collectTypes_hints unfoldTac isConst Ps types k :=
    match Ps with
      | tt => k types
      | (?P1, ?P2) =>
        collectTypes_hints unfoldTac ltac:(isConst) P1 types ltac:(fun types =>
          collectTypes_hints unfoldTac ltac:(isConst) P2 types k)
      | _ =>
        let T := type of Ps in
        let T := eval simpl in T in
        let T := unfoldTac T in
          collectTypes_hint ltac:(isConst) (fun _ : ReifyExpr.VarType unit => T) types k
    end.

  (* Now we repeat this sequence of tactics for reflection itself. *)

  Ltac reify_hint' pcType stateType isConst P types funcs preds vars k :=
    match P with
      | fun x => @?H x -> @?P x =>
        ReifyExpr.reify_expr isConst H types funcs (@nil tvar) vars ltac:(fun _ funcs H =>
          reify_hint' pcType stateType isConst P types funcs preds vars ltac:(fun funcs preds P =>
            let lem := eval simpl in (Build_lemma (types := types) (pcType := pcType) (stateType := stateType)
              vars (H :: Hyps P) (Lhs P) (Rhs P)) in
            k funcs preds lem))
      | fun x => forall cs, @ST.himp _ _ cs (@?L x) (@?R x) =>
        SEP_REIFY.reify_sexpr isConst L types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _uvars funcs preds L =>
          SEP_REIFY.reify_sexpr isConst R types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _uvars funcs preds R =>
            let lem := constr:(Build_lemma (types := types) (pcType := pcType) (stateType := stateType)
              vars nil L R) in
            k funcs preds lem))
      | fun x => _ (@?L x) (@?R x) =>
        SEP_REIFY.reify_sexpr isConst L types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _ funcs preds L =>
          SEP_REIFY.reify_sexpr isConst R types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _ funcs preds R =>
            let lem := constr:(Build_lemma (types := types) (pcType := pcType) (stateType := stateType)
              vars nil L R) in
            k funcs preds lem))
    end.

  Ltac reify_hint pcType stateType isConst P types funcs preds vars k :=
    match P with
      | fun xs : ?T => forall x : ?T', @?f xs x =>
        match T' with
          | PropX.codeSpec _ _ => fail 1
          | _ => match type of T' with
                   | Prop => fail 1
                   | _ =>
                     let P := eval simpl in (fun x : ReifyExpr.VarType (T' * T) =>
                       f (@ReifyExpr.openUp _ T (@snd _ _) x) (@ReifyExpr.openUp _ T' (@fst _ _) x)) in
                     let T' := ReifyExpr.reflectType types T' in
                     reify_hint pcType stateType isConst P types funcs preds (T' :: vars) k
                   | _ => fail 3
                 end
          | _ => fail 2
        end
      | _ => reify_hint' pcType stateType isConst P types funcs preds vars k
    end.

  Ltac reify_hints unfoldTac pcType stateType isConst Ps types funcs preds k :=
    match Ps with
      | tt => k funcs preds (@nil (lemma types pcType stateType)) || fail 2
      | (?P1, ?P2) =>
        reify_hints unfoldTac pcType stateType isConst P1 types funcs preds ltac:(fun funcs preds P1 =>
          reify_hints unfoldTac pcType stateType isConst P2 types funcs preds ltac:(fun funcs preds P2 =>
            k funcs preds (P1 ++ P2)))
        || fail 2
      | _ =>
        let T := type of Ps in
        let T := eval simpl in T in
        let T := unfoldTac T in
          reify_hint pcType stateType isConst (fun _ : ReifyExpr.VarType unit => T) types funcs preds (@nil tvar) ltac:(fun funcs preds P =>
            k funcs preds (P :: nil))
    end.

  (* Build proofs of combined lemma statements *)
  Ltac prove Ps :=
    match Ps with
      | tt => constructor
      | (?P1, ?P2) => 
           (apply Folds.Forall_app; [ prove P1 | prove P2 ])
        || (constructor; [ exact P1 | prove P2 ])
      | _ => constructor; [ exact Ps | constructor ]
    end.


  (* Unfold definitions in a list of types *)
  Ltac unfoldTypes types :=
    match eval hnf in types with
      | nil => types
      | ?T :: ?types =>
        let T := eval hnf in T in
          let types := unfoldTypes types in
            constr:(T :: types)
    end.

  (* Main entry point tactic, to generate a hint database *)
Ltac lift_signature_over_repr s rp :=
  let d := eval simpl Domain in (Domain s) in
  let r := eval simpl Range in (Range s) in
  let den := eval simpl Denotation in (Denotation s) in
  constr:(fun ts' => @Sig (repr rp ts') d r den).

Ltac lift_signatures_over_repr fs rp :=
  match eval hnf in fs with
    | nil => constr:(fun ts' => @nil (signature (repr rp ts')))
    | ?f :: ?fs => 
      let f := lift_signature_over_repr f rp in
      let fs := lift_signatures_over_repr fs rp in
      constr:(fun ts' => (f ts') :: (fs ts'))
  end.

Ltac lift_ssignature_over_repr s rp pc st :=
  let d := eval simpl SDomain in (SDomain s) in
  let den := eval simpl SDenotation in (SDenotation s) in
  constr:(fun ts' => @PSig (repr rp ts') pc st d den).

Ltac lift_ssignatures_over_repr fs rp pc st :=
  match eval hnf in fs with
    | nil => constr:(fun ts' => @nil (predicate (repr rp ts') pc st))
    | ?f :: ?fs => 
      let f := lift_ssignature_over_repr f rp pc st in
      let fs := lift_ssignatures_over_repr fs rp pc st in
      constr:(fun ts' => (f ts') :: (fs ts'))
  end.

Ltac lift_expr_over_repr e rp :=
  match eval hnf in e with
    | @Expr.Const _ ?t ?v => constr:(fun ts => @Expr.Const (repr rp ts) t v)
    | Expr.Var ?v => constr:(fun ts => @Expr.Var (repr rp ts) v)
    | Expr.UVar ?v => constr:(fun ts => @Expr.UVar (repr rp ts) v)
    | Expr.Func ?f ?args =>
      let args := lift_exprs_over_repr args rp in
      constr:(fun ts => @Expr.Func (repr rp ts) f (args ts))
    | Expr.Equal ?t ?l ?r =>
      let l := lift_expr_over_repr l rp in
      let r := lift_expr_over_repr r rp in
      constr:(fun ts => @Expr.Equal (repr rp ts) t (l ts) (r ts))
    | Expr.Not ?e1 =>
      let e1 := lift_expr_over_repr e1 rp in
      constr:(fun ts => @Expr.Not (repr rp ts) (e1 ts))
  end
with lift_exprs_over_repr es rp :=
  match eval hnf in es with
    | nil => constr:(fun ts => @nil (expr (repr rp ts)))
    | ?e :: ?es =>
      let e := lift_expr_over_repr e rp in
      let es := lift_exprs_over_repr es rp in
      constr:(fun ts => e ts :: es ts)
  end.

Ltac lift_sexpr_over_repr e rp pc st :=
  match eval hnf in e with
    | @SE.Emp _ _ _ => constr:(fun ts => @SE.Emp (repr rp ts) pc st)
    | @SE.Inj _ _ _ ?e => 
      let e := lift_expr_over_repr e rp in
      constr:(fun ts => @SE.Inj (repr rp ts) pc st (e ts))
    | @SE.Star _ _ _ ?l ?r =>
      let l := lift_sexpr_over_repr l rp pc st in
      let r := lift_sexpr_over_repr r rp pc st in
      constr:(fun ts => @SE.Star (repr rp ts) pc st (l ts) (r ts))
    | @SE.Exists _ _ _ ?t ?e =>
      let e := lift_sexpr_over_repr e rp pc st in
      constr:(fun ts => @SE.Exists (repr rp ts) pc st t (e ts))
    | @SE.Func _ _ _ ?f ?args => 
      let args := lift_exprs_over_repr args rp in
      constr:(fun ts => @SE.Func (repr rp ts) pc st f (args ts))
    | @SE.Const _ _ _ ?b => constr:(fun ts => @SE.Const (repr rp ts) pc st b)
  end.

Ltac lift_lemma_over_repr lm rp pc st :=
  match eval hnf in lm with
    | {| Foralls := ?f
       ; Hyps := ?h
       ; Lhs := ?l
       ; Rhs := ?r
       |} => 
    let h := lift_exprs_over_repr h rp in
    let l := lift_sexpr_over_repr l rp pc st in
    let r := lift_sexpr_over_repr r rp pc st in
    constr:(fun ts => {| Foralls := f
                       ; Hyps := h ts
                       ; Lhs := l ts
                       ; Rhs := r ts
                       |})
  end.
Ltac lift_lemmas_over_repr lms rp pc st :=
  match lms with
    | nil => constr:(fun ts => @nil (lemma (repr rp ts) pc st))
    | ?lml ++ ?lmr =>
      let lml := lift_lemmas_over_repr lml rp pc st in
      let lmr := lift_lemmas_over_repr lmr rp pc st in
      constr:(fun ts => lml ts ++ lmr ts)
    | ?lm :: ?lms =>
      let lm := lift_lemma_over_repr lm rp pc st in
      let lms := lift_lemmas_over_repr lms rp pc st in
      constr:(fun ts => lm ts :: lms ts)
  end.

Require TypedPackage.
Module Packaged (CE : TypedPackage.CoreEnv).

  (** Package hints together with their environment/parameters. *)
  Record hints := {
    Types : Repr type;
    Functions : forall ts, Repr (signature (repr Types ts));
    PcType : tvar;
    StateType : tvar;
    Predicates : forall ts, Repr (predicate (repr Types ts) PcType StateType);
    Hints : forall ts, hintsPayload (repr Types ts) PcType StateType;
    HintsOk : forall ts fs ps, hintsSoundness (repr (Functions ts) fs) (repr (Predicates ts) ps) (Hints ts)
  }.
  
  Module PACK := TypedPackage.Make SE CE.
  
  Ltac prepareHints unfoldTac pcType stateType isConst env fwd bwd ret :=
    let types := 
      match type of env with
        | PACK.TypeEnv => 
          let ts := eval cbv beta iota zeta delta [ env PACK.applyTypes PACK.Types ] in (PACK.applyTypes env nil) in
          eval simpl in ts
        | PACK.TypeEnv => 
          let ts := eval cbv beta iota zeta delta [ PACK.applyTypes PACK.Types ] in (PACK.applyTypes env nil) in
          eval simpl in ts
      end
    in
    collectTypes_hints unfoldTac isConst fwd (@nil Type) ltac:(fun rt =>
      collectTypes_hints unfoldTac isConst bwd rt ltac:(fun rt =>
        let rt := constr:((pcType : Type) :: (stateType : Type) :: rt) in
        let types := ReifyExpr.extend_all_types rt types in
        let pcT := ReifyExpr.reflectType types pcType in
        let stateT := ReifyExpr.reflectType types stateType in
        let funcs := eval simpl in (PACK.applyFuncs_red env types nil) in
        let preds := eval simpl in (PACK.applyPreds_red env types nil) in
        (reify_hints unfoldTac pcT stateT isConst fwd types funcs preds ltac:(fun funcs preds fwd' =>
          reify_hints unfoldTac pcT stateT isConst bwd types funcs preds ltac:(fun funcs preds bwd' =>
            let types_r := eval cbv beta iota zeta delta [ listToRepr ] in (listToRepr types EmptySet_type) in
            let types_rV := fresh "types" in
            (pose (types_rV := types_r) || fail 1000);
            let funcs_r := lift_signatures_over_repr funcs types_rV in 
            let funcs_r := eval cbv beta iota zeta delta [ listToRepr ] in (fun ts => listToRepr (funcs_r ts) (Default_signature (repr types_rV ts))) in
            let funcs_rV := fresh "funcs" in
            pose (funcs_rV := funcs_r) ;
            let preds_r := lift_ssignatures_over_repr preds types_rV pcT stateT in
            let preds_rV := fresh "preds" in
            let preds_r := eval cbv beta iota zeta delta [ listToRepr ] in (fun ts => listToRepr (preds_r ts) (Default_predicate (repr types_rV ts) pcT stateT)) in
            pose (preds_rV := preds_r) ;
            let fwd' := lift_lemmas_over_repr fwd' types_rV pcT stateT in
            let bwd' := lift_lemmas_over_repr bwd' types_rV pcT stateT in
            let pf := fresh "fwd_pf" in
            assert (pf : forall ts fs ps, hintsSoundness (repr (funcs_rV ts) fs) (repr (preds_rV ts) ps) ({| Forward := fwd' ts ; Backward := bwd' ts |})) by 
              (abstract (constructor; [ prove fwd | prove bwd ])) ;
            let res := constr:(
              {| Types      := types_rV
               ; PcType     := pcT
               ; StateType  := stateT
               ; Functions  := funcs_rV
               ; Predicates := preds_rV
               ; Hints      := fun ts => {| Forward := fwd' ts ; Backward := bwd' ts |}
               ; HintsOk    := pf
               |}) in ret res))))).

  (* Main entry point to simplify a goal *)
(*
  Ltac unfolder isConst hs bound :=
    intros;
      let types := eval simpl in (repr (Types hs) nil) in
      match goal with
        | [ |- ST.himp _ ?P ?Q ] =>
          SEP_REIFY.collectTypes_sexpr isConst P (@nil Type) ltac:(fun rt =>
          SEP_REIFY.collectTypes_sexpr isConst Q rt ltac:(fun rt =>
            let types := extend_all_types rt types in
            let funcs := eval simpl in (repr (Functions hs types) nil) in
            let preds := eval simpl in (repr (Predicates hs types) nil) in
            let pc := eval simpl in (PcType hs) in
            let state := eval simpl in (StateType hs) in
            SEP_REIFY.reify_sexpr isConst P types funcs pc state preds (@nil type) (@nil type) ltac:(fun uvars funcs preds P =>
            SEP_REIFY.reify_sexpr isConst Q types funcs pc state preds (@nil type) (@nil type) ltac:(fun uvars funcs preds Q =>
            let proverC := constr:(@Provers.reflexivityProver_correct types funcs) in
            apply (@unfolderOk types funcs pc state preds (Hints hs types) _ (HintsOk hs types funcs preds) proverC bound P Q)))))
      end.
*)

(*
  Module TESTS.
    Section Tests.
    Variables pc state : Type.

    Variable f : nat -> ST.hprop pc state nil.
    Variable h : bool -> unit -> ST.hprop pc state nil.
    Variable g : bool -> nat -> nat -> nat.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Definition nat_type := {|
      Impl := nat;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None 
                       end
      |}.

    Definition bool_type := {|
      Impl := bool;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None 
                       end
      |}.

    Definition unit_type := {|
      Impl := unit;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None 
                       end
      |}.

    Definition types0 := nat_type :: bool_type :: unit_type :: nil.

Print PACK.TypeEnv.

    Definition env0 : PACK.TypeEnv  :=
      {| PACK.Types := listToRepr 
           ({| Impl := pc ; Eq := fun _ _ => None |} :: 
            {| Impl := state ; Eq := fun _ _ => None |} :: nil) EmptySet_type
       ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
       ; PACK.Preds := fun ts => nil_Repr (SE.Default_predicate _ _ _)
      |}.

    Fixpoint assumptionProver (types : list type) (Hs : list (expr types)) (P : expr types) :=
      match Hs with
        | nil => false
        | H :: Hs' => match expr_seq_dec H P with
                        | Some _ => true
                        | None => assumptionProver Hs' P
                      end
      end.

    Hypothesis Hemp : forall cs, ST.himp cs (ST.emp pc state) (ST.emp pc state).
    Hypothesis Hf : forall cs, ST.himp cs (f 0) (ST.emp _ _).
    Hypothesis Hh : forall cs, ST.himp cs (h true tt) (ST.star (h true tt) (f 13)).

    Hypothesis Hf0 : forall n cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh0 : forall b u cs, ST.himp cs (h b u) (ST.star (h (negb b) tt) (f 13)).

    Hypothesis Hf1 : forall n, n <> 0 -> forall cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh1 : forall b u, b = false -> u <> tt -> forall cs, ST.himp cs (h b u) (ST.star (h b tt) (f 13)).


    (** * Creating hint databases *)

    Ltac prepare := prepareHints ltac:(fun x => x) pc state isConst env0.

    Definition hints_emp : hints.
      prepare (Hemp, Hf) (Hemp, Hf, Hh) ltac:(fun x => refine x).
    Defined.

    Definition hints_tt : hints.
      prepare tt tt ltac:(fun x => refine x).
    Defined.
    End Tests.
  End TESTS.
*)
End Packaged.

End Make.


(*
      Theorem unify_args' : forall tfuncs tU tG U G l r D R f  S S',
        U.Subst_WellTyped tfuncs tU tG S ->
        all2 (@is_well_typed _ tfuncs tU tG) l D = true ->
        all2 (@is_well_typed _ tfuncs tU tG) r D = true ->
        fold_left_2_opt (U.exprUnify unify_bound) l r S = Some S' ->
        U.Subst_equations funcs U G S ->
        @applyD types (exprD funcs U G) D (map (U.exprInstantiate S') l) R f =
        @applyD types (exprD funcs U G) D (map (U.exprInstantiate S') r) R f /\
        U.Subst_equations funcs U G S' /\
        U.Subst_Extends S' S /\
        U.Subst_WellTyped tfuncs tU tG S'.
      Proof.
        induction l; destruct D; try congruence; simpl in *; intros;
          repeat match goal with
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                   | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
                     revert H ; case_eq X ; intros; try congruence
                   | [ |- _ ] => progress ( simpl in * )
                   | [ |- _ ] => progress subst
                   | [ H : U.exprUnify _ _ _ _ = Some _ |- _ ] => 
                     generalize H ; generalize H; 
                     apply U.exprUnify_Extends in H ;
                     let H := fresh "H" in
                     intro H ;
                     apply U.exprUnify_sound in H
                 end; try solve [ intuition ].
        { 
          

          generalize H4; generalize H4; apply U.exprUnify_Extends in H4; auto.
          intro. eapply U.exprUnify_WellTyped in H7; eauto.

 generalize H4. eapply U.exprUnify_sound in H4.
          
          



*)
