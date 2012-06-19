Require Import Arith Bool EqdepClass List.

Require Import Heaps (* Reflect *).
Require Import Expr ExprUnify Folds.
Require Import SepExpr SepHeap.
Require Import Prover.
Require Import Env.
Require Import Reflection Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Require NatMap.

Module FM := NatMap.IntMap.

Fixpoint allb A (P : A -> bool) (ls : list A) : bool :=
  match ls with
    | nil => true
    | x :: ls' => P x && allb P ls'
  end.

Lemma nth_error_None_length : forall (T : Type) (ls : list T) (n : nat),
  nth_error ls n = None -> length ls <= n.
Proof.
  induction ls; destruct n; simpl; intros; think; try omega. inversion H.
  eapply IHls in H. omega.
Qed.

Lemma applyD_impl_Forall : forall types F F' P Dom args R D v,
  applyD (types := types) F Dom args R D = Some v ->
  Forall P args ->
  (forall x y v, P x -> F x y = Some v -> F' x y = Some v) ->
  applyD F' Dom args R D = Some v.
Proof.
  induction Dom; destruct args; simpl; intros; think; auto. inversion H0; subst; intros.
  erewrite H1; eauto.
Qed.

Lemma applyD_impl : forall types F F' Dom args R D,
  (forall x y, F x y = F' x y) ->
  applyD (types := types) F Dom args R D = applyD F' Dom args R D.
Proof.
  induction Dom; destruct args; simpl; intros; think; auto.
  destruct (F' e a); auto.
Qed.

Lemma applyD_map : forall types F F' Dom args R D,
  applyD (types := types) F Dom (map F' args) R D = applyD (fun x y => F (F' x) y) Dom args R D.
Proof.
  induction Dom; destruct args; simpl; intros; think; auto.
  destruct (F (F' e) a); auto.
Qed.

Lemma map_nth_error_full : forall T U (F : T -> U) ls n,
  nth_error (map F ls) n = match nth_error ls n with
                             | None => None
                             | Some v => Some (F v)
                           end.
Proof.
  induction ls; destruct n; simpl; intros; think; auto.
Qed.


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

    Section openForUnification.
      Variable U : nat. (** **)

      Definition ERROR : expr types.
      refine (Var 0).
      Qed.
      
      Fixpoint openForUnification (e : expr types) : expr types :=
        match e with
          | Expr.Const _ _ => e
          | Var v => UVar (U + v)
          | UVar _ => e (** contradiction **)
          | Expr.Func f es => Expr.Func f (List.map openForUnification es)
          | Equal t l r => Equal t (openForUnification l) (openForUnification r)
          | Not e => Not (openForUnification e)
        end.

    End openForUnification.

    Section instantiate.
      Variable doQuant : nat -> expr types.
      Variable U : nat.
      Variable G' : nat.
      Variable sub : U.Subst types.
      
      Fixpoint liftInstantiate (e : expr types) : expr types :=
        match e with
          | Expr.Const _ _ => e
          | Var v => 
            if NPeano.ltb v G' then doQuant v (* Var (v + G) *)
            else let idx := U + v - G' in 
                 match U.Subst_lookup idx sub with
                   | None => UVar idx (** contradiction **)
                   | Some e => e
                 end
          | UVar v => match U.Subst_lookup v sub with (** contradiction **)
                        | None => UVar v
                        | Some e => e
                      end
          | Expr.Func f es => Expr.Func f (List.map liftInstantiate es)
          | Equal t l r => Equal t (liftInstantiate l) (liftInstantiate r)
          | Not e => Not (liftInstantiate e)
        end.

    End instantiate.

    Definition quantFwd (over : nat) (v : nat) : expr types :=  Var (v + over).
    Definition quantBwd (over : nat) (v : nat) : expr types :=  UVar (v + over).

    Class QuantifierSpec U G (quant : nat -> expr types) (BuildUVars BuildVars : env types -> env types -> env types) : Prop :=
    { Weakenable : forall funcs F e t v, 
      exprD funcs U G e t = Some v ->
      exprD funcs (BuildUVars U F) (BuildVars G F) e t = Some v
    ; PreservesVar : 
      forall funcs F v t,
      is_well_typed (typeof_funcs funcs) nil (typeof_env F) (Var (types := types) v) t = true ->
      exprD funcs nil F (Var v) t = exprD funcs (BuildUVars U F) (BuildVars G F) (quant v) t
    }.
    Instance QuantifierSpec_Fwd U G : QuantifierSpec U G (quantFwd (length G)) (fun x _ => x) (fun x y => x ++ y).
    constructor.
    { intros. rewrite <- app_nil_r with (l := U). eapply exprD_weaken; auto. }
    { intros. simpl; unfold lookupAs; simpl.
      rewrite nth_error_app_R. cutrewrite (v + length G - length G = v); [ | omega ]. reflexivity. omega. }
    Qed.

    Instance QuantifierSpec_Bwd U G : QuantifierSpec U G (quantBwd (length U)) (fun x y => x ++ y) (fun x _ => x).
    constructor.
    { intros. rewrite <- app_nil_r with (l := G). eapply exprD_weaken; auto. }
    { intros. simpl; unfold lookupAs; simpl.
      rewrite nth_error_app_R. cutrewrite (v + length U - length U = v); [ | omega ]. reflexivity. omega. }
    Qed.

    Definition applySHeap (F : expr types -> expr types) (sh : SHeap types pcType stateType) : SHeap types pcType stateType :=
      {| impures := MM.mmap_map (map F) (impures sh)
       ; pures := map F (pures sh)
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
      WellTyped_lemma (typeof_funcs funcs) (typeof_preds preds) lem = true /\
      forallEachR (Foralls lem) (fun env =>
        implyEach (Hyps lem) meta_base (var_base ++ env)
        (forall specs, himp funcs preds meta_base (var_base ++ env) specs (Lhs lem) (Rhs lem))).

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
      Definition applicable quant (firstUvar : nat) (lem : lemma) (args key : exprs types) 
        : option (U.Subst types) :=
        let numForalls := length (Foralls lem) in
        (** NOTE: it is important that [key] is first because of the way the unification algorithm works **)
        match fold_left_2_opt (U.exprUnify unify_bound) (map (openForUnification firstUvar) key) args (U.Subst_empty _) with
          | None => None
          | Some subst =>
            if EqNat.beq_nat (U.Subst_size subst) numForalls && checkAllInstantiated firstUvar (Foralls lem) subst
            then (* Now we must make sure all of the lemma's pure obligations are provable. *)
                 if allb (Prove prover facts) (map (liftInstantiate quant firstUvar 0 subst) (Hyps lem))
                 then Some subst
                 else None
            else None
        end.

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
                    match applicable (quantFwd firstVar) firstUvar h args args' with
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
*)
                          (* Remove the current call from the state, as we are about to replace
                           * it with a simplified set of pieces. *)
                          let impures' := FM.add f argss (impures (Heap s)) in
                          let sh := {| impures := impures'
                                     ; pures := pures (Heap s)
                                     ; other := other (Heap s) |} in

                          (* Time to hash the hint RHS, to (among other things) get the new existential variables it creates. *)
                          let (exs, sh') := hash (Rhs h) in

                          (* Apply the substitution that unification gave us. *)
                          let sh' := applySHeap (liftInstantiate (quantFwd firstVar) firstUvar (length exs) subs) sh' in

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
        let imps       := SH.impures (Heap s) in
        let firstUvar  := length (UVars s) in
        let firstVar   := length (Vars s) in
        find (fun h =>
          match Rhs h with
            | Func f args' =>
              match FM.find f imps with
                | None => None
                | Some argss => 
                  findWithRest (fun args argss =>
                    match applicable (quantBwd firstUvar) firstUvar h args args' with
                      | None => None
                      | Some subs =>
(*
                    let args' := map (exprSubstU O (length (Foralls h)) firstUvar) args' in

                    (* Unify the respective function arguments. *)
                    match fold_left_2_opt (U.exprUnify unify_bound) args' args (U.Subst_empty _) with
                      | None => None
                      | Some subs =>
                        (* Now we must make sure all of the lemma's pure obligations are provable. *)
                        if allb (Prove prover facts) (map (substExprBw firstUvar O subs) (Hyps h)) then
*)
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
                          let sh' := applySHeap (liftInstantiate (quantBwd firstUvar) firstUvar (length exs) subs) sh' in

                          (* The final result is obtained by joining the hint LHS with the original symbolic heap. *)
                          Some {| Vars := Vars s
                                ; UVars := UVars s ++ rev exs
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

      Lemma Subst_to_env_nth_error_lookup : forall F U G sub x v CUR,
        Subst_to_env U G sub (typeof_env F) CUR = Some F ->
        nth_error F x = Some v ->
        exists e, U.Subst_lookup (CUR + x) sub = Some e /\
          exprD funcs U G e (projT1 v) = Some (projT2 v).
      Proof.
        induction F; simpl; intros; think.
        { destruct x; simpl in *; unfold error in *; congruence. }
        { destruct a; simpl in *. think. apply inj_pair2 in H5. subst.
          destruct x; simpl in *. 
          { inversion H0; clear H0; subst. rewrite Plus.plus_0_r. eexists; intuition eauto. }
          { rewrite Plus.plus_comm. simpl. rewrite Plus.plus_comm. eapply IHF in H1. simpl in H1. eapply H1. auto. } }
      Qed.
      Lemma Subst_to_env_typeof_env : forall U G sub ts CUR F,
        Subst_to_env U G sub ts CUR = Some F ->
        ts = typeof_env F.
      Proof.
        induction ts; simpl; intros.
        { think. reflexivity. }
        { consider (Subst_to_env U G sub ts (S CUR)). intros. eapply IHts in H. think. simpl. auto.
          intros; think. }
      Qed.

      Lemma nth_error_typeof_funcs : forall f t s,
        nth_error (typeof_funcs funcs) f = Some t ->
        nth_error funcs f = Some s ->
        TRange t = Range s /\ TDomain t = Domain s.
      Proof.
        unfold typeof_funcs. intros. erewrite map_nth_error in H by eauto. think. unfold typeof_sig; intuition.
      Qed.

      Lemma typeof_env_length : forall types g, 
        length (typeof_env (types := types) g) = length g.
      Proof.
        intros. apply map_length.
      Qed.

      Theorem openForUnification_spec : forall F U G e t ,
        is_well_typed (typeof_funcs funcs) nil (typeof_env F) e t = true ->
        exprD funcs nil F e t = exprD funcs (U ++ F) G (openForUnification (length U) e) t.
      Proof.
        induction e; simpl; unfold lookupAs; intros; think;
          repeat match goal with
                   | [ H : nth_error _ _ = Some _ |- _ ] =>  
                     eapply WellTyped_env_nth_error_Some in H; [ | solve [ eauto using typeof_env_WellTyped_env ] ] ; destruct H
                   | [ |- _ ] => rewrite nth_error_app_R by omega
                   | [ |- _ ] => rewrite nth_error_app_L by omega
                   | [ H : nth_error ?L ?n = _ |- context [ nth_error ?L ?n' ] ] =>
                     cutrewrite (n' = n); [ | omega ]
                   | [ H : nth_error nil ?X = Some _ |- _ ] =>
                     clear - H ; abstract (exfalso ; destruct X ; simpl in *; unfold error in *; congruence)
                   | [ |- match ?X with _ => _ end = match ?X with _ => _ end ] =>
                     consider X; intros; try reflexivity
                 end; think; auto.
        eapply nth_error_typeof_funcs in H2; eauto. intuition. think.
        { rewrite applyD_map.
          revert H1. destruct s; simpl in *. clear H5. generalize dependent Domain. clear - H.
          induction H; destruct Domain; intros; simpl in *; think; auto.
          consider (exprD funcs (U ++ F) G (openForUnification (length U) x) t); intros; auto. }
      Qed.

      Theorem openForUnification_typed : forall F U G e t ,
        is_well_typed (typeof_funcs funcs) nil F e t = true ->
        is_well_typed (typeof_funcs funcs) (U ++ F) G (openForUnification (length U) e) t = true.
      Proof.
        induction e; simpl; unfold lookupAs; intros; think;
          repeat match goal with
                   | [ H : nth_error _ _ = Some _ |- _ ] =>  
                     eapply WellTyped_env_nth_error_Some in H; [ | solve [ eauto using typeof_env_WellTyped_env ] ] ; destruct H
                   | [ |- _ ] => rewrite nth_error_app_R by omega
                   | [ |- _ ] => rewrite nth_error_app_L by omega
                   | [ H : nth_error ?L ?n = _ |- context [ nth_error ?L ?n' ] ] =>
                     cutrewrite (n' = n); [ | omega ]
                   | [ H : nth_error nil ?X = Some _ |- _ ] =>
                     clear - H ; abstract (exfalso ; destruct X ; simpl in *; unfold error in *; congruence)
                   | [ |- match ?X with _ => _ end = match ?X with _ => _ end ] =>
                     consider X; intros; try reflexivity
                 end; think; auto.
        { rewrite EquivDec_refl_left. reflexivity. }
        { destruct t0; simpl in *. clear H0. generalize dependent TDomain. induction H; destruct TDomain; simpl in *; auto.
          intros; think; auto. }
      Qed.

      Theorem liftInstantiate_spec : forall U G quant (BuildUVars BuildVars : env types -> env types -> env types),
        QuantifierSpec U G quant BuildUVars BuildVars ->
        forall G' F e t sub ts,
          is_well_typed (typeof_funcs funcs) nil (typeof_env G' ++ typeof_env F) e t = true ->
          Subst_to_env U G sub ts (length U) = Some F ->
          exprD funcs nil (G' ++ F) e t =
          exprD funcs (BuildUVars U G') (BuildVars G G') (liftInstantiate quant (length U) (length G') sub e) t.
      Proof.
        induction e; repeat progress (simpl in *; unfold lookupAs in *; intros; 
          repeat match goal with
                   | [ H : nth_error _ _ = Some _ |- _ ] =>  
                     eapply WellTyped_env_nth_error_Some in H; [ | solve [ eauto using typeof_env_WellTyped_env ] ] ; destruct H
                   | [ |- _ ] => rewrite nth_error_app_R by omega
                   | [ |- _ ] => rewrite nth_error_app_L by omega
                   | [ |- _ ] => rewrite nth_error_app_R in * by omega
                   | [ |- _ ] => rewrite nth_error_app_L in * by omega
                   | [ H : nth_error ?L ?n = _ |- context [ nth_error ?L ?n' ] ] =>
                     cutrewrite (n' = n); [ | omega ]
                   | [ H : nth_error nil ?X = Some _ |- _ ] =>
                     clear - H ; abstract (exfalso ; destruct X ; simpl in *; unfold error in *; congruence)
                   | [ |- match ?X with _ => _ end = match ?X with _ => _ end ] =>
                     consider X; intros; try reflexivity
                   | [ |- context [ NPeano.ltb ?X ?Y ] ] => consider (NPeano.ltb X Y); intros
                 end; think); auto.
        { eapply H. rewrite nth_error_app_L in H0. simpl in *. unfold typeof_env in *. 
          repeat rewrite map_nth_error_full in *. consider (nth_error G' x). intros; think.
          rewrite EquivDec_refl_left. auto. congruence. rewrite typeof_env_length. auto. }
        { rewrite nth_error_app_R in H0. 2: rewrite typeof_env_length; auto.
          rewrite typeof_env_length in *. unfold typeof_env in *. rewrite map_nth_error_full in *.
          generalize (Subst_to_env_typeof_env _ _ _ _ _ H1); intros; subst.
          consider (nth_error F (x - length G')); intros; try congruence.
          eapply Subst_to_env_nth_error_lookup in H1; eauto. inversion H3; clear H3; subst. destruct H1. intuition.
          cutrewrite (length U + (x - length G') = length U + x - length G') in H3; [ | omega ].
          rewrite H3. rewrite EquivDec_refl_left. symmetry. eapply Weakenable. eauto. }
        { unfold typeof_funcs in H1; rewrite map_nth_error_full in H1. rewrite H3 in H1. inversion H1; clear H1; subst.
          unfold typeof_sig in *. simpl in *. destruct s. revert H5 H2. clear - H0. generalize dependent Domain.
          induction H0; destruct Domain; simpl in *; intros; think; auto.
          erewrite <- H; eauto. destruct (exprD funcs nil (G' ++ F) x t); auto. }
      Qed.

      Theorem liftInstantiate_typed : forall U G quant (BuildUVars BuildVars : env types -> env types -> env types),
        QuantifierSpec U G quant BuildUVars BuildVars ->
        forall G' F e t sub ts,
          is_well_typed (typeof_funcs funcs) nil (typeof_env G' ++ typeof_env F) e t = true ->
          Subst_to_env U G sub ts (length U) = Some F ->
          is_well_typed (typeof_funcs funcs) nil (typeof_env (G' ++ F)) e t = true ->
          is_well_typed (typeof_funcs funcs) (typeof_env (BuildUVars U G')) (typeof_env (BuildVars G G')) 
          (liftInstantiate quant (length U) (length G') sub e) t = true.
      Proof.
        intros. eapply is_well_typed_correct in H2; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
        2: instantiate (1 := nil); reflexivity. destruct H2. erewrite liftInstantiate_spec in H2 by eassumption.
        eapply is_well_typed_correct_only in H2; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
      Qed.

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

      Lemma openForUnification_liftInstantiate : forall quant sub U e,
        U.exprInstantiate sub (openForUnification U e) = liftInstantiate quant U 0 sub e.
      Proof.
        induction e; simpl; intros; think;
          repeat (rewrite U.exprInstantiate_Const || 
                  rewrite U.exprInstantiate_Equal || 
                  rewrite U.exprInstantiate_Func || 
                  rewrite U.exprInstantiate_Not ||
                  rewrite U.exprInstantiate_Var ||
                  rewrite U.exprInstantiate_UVar);
          think; auto.
        { rewrite <- minus_n_O. reflexivity. }
        { clear - H. f_equal. induction H; simpl; intros; think; auto. }
      Qed.

      Lemma typeof_funcs_WellTyped_funcs_eq : forall tfuncs funcs,
        WellTyped_funcs (types := types) tfuncs funcs ->
        tfuncs = typeof_funcs funcs.
      Proof.
        clear. induction 1; auto. simpl. f_equal; auto. unfold WellTyped_sig, typeof_sig in *.
        destruct r; destruct l; intuition; f_equal; auto.
      Qed.

      Lemma checkAllInstantiated_app : forall sub ts ts' from,
        checkAllInstantiated from (ts ++ ts') sub = 
        checkAllInstantiated from ts sub && checkAllInstantiated (length ts + from) ts' sub.
      Proof.
        clear. induction ts; simpl; intros; think; eauto; simpl.
        consider (U.Subst_lookup from sub); intros; auto.
        f_equal. rewrite Plus.plus_comm. simpl. rewrite Plus.plus_comm. reflexivity.
      Qed.

      Lemma Subst_to_env_app : forall U G sub ts ts' from, 
        Subst_to_env U G sub (ts ++ ts') from = 
        match Subst_to_env U G sub ts from , Subst_to_env U G sub ts' (length ts + from) with
          | Some l , Some r => Some (l ++ r)
          | _ , _ => None
        end.
      Proof.
        induction ts; intros; simpl; think; auto.
        destruct (Subst_to_env U G sub ts' from); auto.
        cutrewrite (S (length ts + from) = length ts + S from); [ | omega ].
        repeat match goal with 
                 | [ |- context [ match ?X with _ => _ end ] ] => 
                   match X with 
                     | match _ with _ => _ end => fail 1
                     | _ => destruct X
                   end
               end; auto.
      Qed.

      Lemma range_dropU : forall U G (e : expr types) t U',
        is_well_typed (typeof_funcs funcs) (U ++ U') G e t = true ->
        (forall n, n >= length U -> n < length U + length U' -> mentionsU n e = false) ->
        is_well_typed (typeof_funcs funcs) U G e t = true.
      Proof.
        clear. induction U' using rev_ind; intros.
        rewrite app_nil_r in *; auto.
        rewrite <- app_ass in H. eapply is_well_typed_not_mentionsU_last in H. eapply IHU'; eauto.
        intros. eapply H0; auto. rewrite app_length. simpl. omega.
        eapply H0; rewrite app_length; try omega. rewrite app_length. simpl. omega.
      Qed.

      Lemma checkAllInstantiated_dropU : forall tU tG tfuncs sub ts ts',
        checkAllInstantiated (length tU) ts sub = true ->
        U.Subst_WellTyped tfuncs (tU ++ ts ++ ts') tG sub ->
        forall e t n,
          n >= length tU ->
          is_well_typed tfuncs (tU ++ ts) tG e t = true ->
          U.Subst_lookup n sub = Some e ->
          is_well_typed tfuncs tU tG e t = true.
      Proof.
        clear. induction ts using rev_ind; simpl; intros; think; eauto.
        rewrite app_nil_r in *. auto.
        rewrite checkAllInstantiated_app in H. simpl in *; think. 
        eapply IHts; eauto. rewrite app_ass in H0. simpl in *; eauto.
        eapply is_well_typed_not_mentionsU_last. rewrite app_ass. eassumption.
        eapply U.exprInstantiate_Removes. rewrite app_length. rewrite Plus.plus_comm; eauto.
        instantiate (1 := e). eapply U.exprInstantiate_instantiated. eauto.
      Qed.

      Lemma checkAllInstantiated_Subst_to_env_success : forall U G tU tG tfuncs, 
        WellTyped_env tU U ->
        WellTyped_env tG G ->
        WellTyped_funcs tfuncs funcs ->
        forall sub ts ts',
          checkAllInstantiated (length tU) (ts ++ ts') sub = true ->
          U.Subst_WellTyped tfuncs (tU ++ ts ++ ts') tG sub ->
          exists env, Subst_to_env U G sub ts (length tU) = Some env.
      Proof.
        clear; induction ts using rev_ind; simpl; intros; think; eauto.
        { rewrite app_ass in *. simpl in *. generalize H2. eapply IHts in H2. 2: eauto.
          destruct H2. rewrite Subst_to_env_app. rewrite H2. simpl.
          intro XX. generalize XX. rewrite checkAllInstantiated_app in XX. simpl in XX. think.
          generalize H5. eapply U.WellTyped_lookup in H5; eauto. destruct H5. intuition.
          eapply checkAllInstantiated_dropU in XX. 5: eapply H7. 4: eauto.
          3: omega. Focus 2. instantiate (1 := nil). repeat rewrite app_ass. simpl. rewrite app_nil_r. auto.
          repeat rewrite nth_error_app_R in H8 by omega. repeat rewrite map_length in H8.
          cutrewrite (length ts + length U - length U - length ts = 0) in H8; [ | omega ]. inversion H8. subst.
          eapply is_well_typed_correct in XX.
          4: eauto. 2: unfold WellTyped_env in *; auto. 2: unfold WellTyped_env in *; auto.
          destruct XX. rewrite H5. eauto. }
      Qed.
      

      (** TODO: lift this outside **)
      Lemma fold_left_2_opt_unify : forall tU tG ts args args' sub sub',
        U.Subst_WellTyped (types := types) (typeof_funcs funcs) tU tG sub -> 
        all2 (is_well_typed (typeof_funcs funcs) tU tG) args ts = true ->
        all2 (is_well_typed (typeof_funcs funcs) tU tG) args' ts = true ->
        fold_left_2_opt (U.exprUnify unify_bound) args args' sub = Some sub' ->
        U.Subst_WellTyped (typeof_funcs funcs) tU tG sub' /\
        U.Subst_Extends sub' sub /\
        map (U.exprInstantiate sub') args = map (U.exprInstantiate sub') args'.
      Proof.
        clear. induction ts; destruct args; destruct args'; intros; simpl in *; think; 
        try (congruence || solve [ intuition (eauto; reflexivity) ]). 
        do 2 generalize H2. apply U.exprUnify_sound in H2. intro. eapply U.exprUnify_Extends in H6.
        intro. eapply U.exprUnify_WellTyped in H7; eauto. eapply IHts in H3; eauto. destruct H3.
        intuition. etransitivity; eauto. rewrite H10. f_equal.
        assert (U.exprInstantiate sub' (U.exprInstantiate s e) = U.exprInstantiate sub' (U.exprInstantiate s e0)).
        rewrite H2. reflexivity. repeat rewrite U.exprInstantiate_Extends in H8 by eauto. auto.
      Qed.

      Lemma implyEach_sem : forall cc U G es,
        implyEach es U G cc <-> (AllProvable funcs U G es -> cc).
      Proof. clear; induction es; simpl; intuition. Qed.

      Lemma liftInstantiate_lemmaD : forall quant BuildUVars BuildVars U G,
        QuantifierSpec U G quant BuildUVars BuildVars ->
        forall lem sub env,
        Subst_to_env U G sub (Foralls lem) (length U) = Some env ->
        lemmaD nil nil lem ->            
        implyEach (map (liftInstantiate quant (length U) 0 sub) (Hyps lem)) U G
        (forall specs : PropX.codeSpec (tvarD types pcType) (tvarD types stateType),
          himp funcs preds nil env specs (Lhs lem) (Rhs lem)). 
      Proof.
        clear. destruct 3; simpl in *. eapply forallEachR_sem in H2; eauto using Subst_to_env_env.
        eapply implyEach_sem. intros. eapply implyEach_sem in H2; eauto.
        
        clear H2 specs. unfold WellTyped_lemma in *. think. generalize dependent (Hyps lem).
        induction l; simpl; intros; auto. think. intuition. clear H6 H8.
        unfold Provable in *.
        generalize (liftInstantiate_spec H nil (F := env)). simpl. erewrite <- Subst_to_env_typeof_env by eassumption.
        intro. eapply H6 in H1; eauto. rewrite H1.
        consider (exprD funcs U G (liftInstantiate quant (length U) 0 sub a) tvProp); try contradiction; intros.
        generalize (Weakenable _ nil _ _ H3). intro. rewrite H8. auto.
      Qed.
      Lemma allb_AllProvable : forall U G facts hyps,
        Valid PC U G facts ->
        allb (fun x => is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G) x tvProp) hyps = true ->
        allb (Prove prover facts) hyps = true ->
        AllProvable funcs U G hyps.
      Proof.
        clear. induction hyps; simpl; intros; think; auto.
        intuition; eauto. eapply Prove_correct; eauto. unfold ValidProp.
        eapply is_well_typed_correct; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
      Qed.          
      Lemma himp_existsEach_ST_EXT_existsEach : forall cs U P vars G,
        ST.heq cs (sexprD funcs preds U G (SE.existsEach vars P)) 
        (ST_EXT.existsEach vars (fun env => sexprD funcs preds U (rev env ++ G) P)).
      Proof.
        Opaque ST_EXT.existsEach.
        induction vars; simpl; intros. rewrite ST_EXT.existsEach_nil. simpl. reflexivity.
        change (a :: vars) with ((a :: nil) ++ vars). rewrite ST_EXT.existsEach_app.
        rewrite ST_EXT.existsEach_cons. apply ST.heq_ex. intros. rewrite ST_EXT.existsEach_nil. rewrite IHvars.
        simpl. eapply ST_EXT.heq_existsEach. intros. rewrite app_ass. reflexivity.
      Qed.
      Lemma exprInstantiate_noop : forall sub (e : expr types),
        (forall u, mentionsU u e = true -> U.Subst_lookup u sub = None) ->
        U.exprInstantiate sub e = e.
      Proof.
        clear; induction e; simpl in *; intros; 
          repeat (rewrite U.exprInstantiate_Const || 
            rewrite U.exprInstantiate_Equal || 
              rewrite U.exprInstantiate_Func || 
                rewrite U.exprInstantiate_Not ||
                  rewrite U.exprInstantiate_Var ||
                    rewrite U.exprInstantiate_UVar); think; try congruence; auto.
        { rewrite H; auto. consider (beq_nat x x); auto. }
        { f_equal. revert H0. induction H; simpl; intros; think; auto.
          erewrite IHForall; try erewrite H; eauto; intros; eapply H1; think; auto using orb_true_r. }
        { erewrite IHe1; try erewrite IHe2; eauto; intros; eapply H; think; auto using orb_true_r. }
      Qed.

      Parameter Subst_size_cardinal : forall sub n,
        U.Subst_size (types := types) sub = n ->
        exists ls, NoDup ls /\ length ls = n /\
          (forall u, In u ls <-> ~(U.Subst_lookup u sub = None)). 

      Lemma independent_well_typed : forall sub F cU,
        beq_nat (U.Subst_size sub) (length F) = true ->
        checkAllInstantiated cU F sub = true ->
        forall u, u <= cU -> U.Subst_lookup u sub = None.
      Proof.
        clear. intros. symmetry in H. apply beq_nat_eq in H. 
        eapply Subst_size_cardinal in H.
(*
        Lemma checkAllInstantiated_domain : forall sub F F' cU,
          checkAllInstantiated cU (F ++ F') sub = true ->
          U.Subst_size sub = length (F ++ F') ->
          (forall u, cU + length F <= u -> u < cU + length F + length F' -> U.Subst_lookup u sub <> None) ->
          forall u, u < cU -> U.Subst_lookup u sub = None.
        Proof.
          clear. induction F using rev_ind; intros; simpl in *.
          { eapply Subst_size_cardinal in H0. destruct H0. intuition.
            consider (U.Subst_lookup u sub); auto. intros. exfalso.
            assert (In u x). eapply H5. intro. congruence.
            

            cut (~In u x). intros. 


 }
          { rewrite app_ass in *; simpl in *. eapply IHF; eauto.
            rewrite checkAllInstantiated_app in H. simpl in *. think.
            consider (EqNat.beq_nat (length F + cU) u0). intros. subst. intro. congruence.
            intros. eapply H1. rewrite app_length. simpl. omega. rewrite app_length. simpl. omega. }
        Qed.       

            

          clear. induction F; simpl in *; intros; think. exfalso. omega.
          consider (EqNat.beq_nat cU u); intros. subst. 
          intro. congruence. eapply IHF; eauto. omega. omega.
        Qed.

        Lemma checkAllInstantiated_domain : forall sub F cU,
          checkAllInstantiated cU F sub = true ->
          forall u, cU <= u -> u < cU + length F -> ~(U.Subst_lookup u sub = None).
        Proof.
          clear. induction F; simpl in *; intros; think. exfalso. omega.
          consider (EqNat.beq_nat cU u); intros. subst. 
          intro. congruence. eapply IHF; eauto. omega. omega.
        Qed.
        generalize (checkAllInstantiated_domain _ H0); intros.
        destruct H. intuition.
*)
        
      Admitted.
      Lemma is_well_typed_mentionsU : forall U G (e : expr types) t,
        is_well_typed (typeof_funcs funcs) U G e t = true ->
        forall u, mentionsU u e = true -> u < length U.
      Proof.
        clear. induction e; simpl; intros; try solve [ think; auto ].
        think. apply nth_error_Some_length in H. auto.
        { consider (nth_error (typeof_funcs funcs) f). intros. consider (equiv_dec t (TRange t0)); think; intros.
          clear H0. destruct t0; simpl in *. generalize dependent TDomain. revert H1. 
          induction H; try congruence; destruct TDomain; simpl in *; think; try congruence; intros.
          consider (is_well_typed (typeof_funcs funcs) U G x t); intros. apply orb_true_iff in H1. destruct H1.
          eapply H; eauto. eapply IHForall; eauto. }
        { destruct t0. apply andb_true_iff in H. apply orb_true_iff in H0. destruct H. destruct H0; eauto. congruence. }
        { destruct t; try congruence. eapply IHe; eauto. }
      Qed.
      Lemma applySHeap_spec : forall cs U G U' G' s F,
        (forall e t, 
          is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G) e t = true ->
          exprD funcs U G e t = exprD funcs U' G' (F e) t) ->
        SE.ST.heq cs (sexprD funcs preds U G (sheapD s))
                     (sexprD funcs preds U' G' (sheapD (applySHeap F s))).
      Proof.
(*
        clear. intros. do 2 rewrite SH.sheapD_def. simpl. repeat eapply SE.ST.heq_star_frame.
        { eapply MM.PROPS.map_induction with (m := impures s); intros.
          repeat rewrite SH.impuresD_Empty by eauto using MF.map_Empty. reflexivity.
          rewrite SH.impuresD_Add by eauto using MF.map_Add, MF.map_not_In.
          symmetry. unfold MM.mmap_map in *. rewrite SH.impuresD_Add. 2: eapply MF.map_Add; eauto. 
          2: eapply MF.map_not_In; eauto.
          simpl. symmetry. apply ST.heq_star_frame; eauto.
          cut (ST.heq cs (sexprD funcs preds U G SE.Emp) (sexprD funcs preds U' G' SE.Emp)); [ | reflexivity ].
          generalize (@SE.Emp types pcType stateType). revert H. clear.
          induction e; simpl; intros. repeat rewrite starred_nil. auto.
          repeat rewrite starred_cons. simpl. apply ST.heq_star_frame; eauto. 
          destruct (nth_error preds x); try reflexivity.
          rewrite applyD_map. erewrite applyD_impl. reflexivity. intros. simpl. eauto. }
        { cut (ST.heq cs (sexprD funcs preds U G SE.Emp) (sexprD funcs preds U' G' SE.Emp)); [ | reflexivity ].
          generalize (@SE.Emp types pcType stateType). induction (pures s); intros; 
          repeat (rewrite starred_nil || rewrite starred_cons); auto. simpl map. rewrite starred_cons.
          simpl. rewrite IHl; eauto. rewrite H. reflexivity. }
        { cut (ST.heq cs (sexprD funcs preds U G SE.Emp) (sexprD funcs preds U' G' SE.Emp)); [ | reflexivity ].
          generalize (@SE.Emp types pcType stateType). induction (other s); intros.
          etransitivity. rewrite starred_nil. reflexivity. etransitivity; [ | rewrite starred_nil; reflexivity ].
          auto.
          
          etransitivity; [ rewrite starred_cons; reflexivity | ].
          etransitivity; [ |  rewrite starred_cons; reflexivity ]. simpl. rewrite IHl; eauto. reflexivity. }
*)
      Admitted.
      Lemma typeof_env_app : forall l r,
        typeof_env (types := types) l ++ typeof_env r = typeof_env (l ++ r).
      Proof.
        clear; induction l; simpl; intros; think; auto.
      Qed.

      Theorem applicableOk : forall quant (BuildUVars BuildVars : env types -> env types -> env types) U G,
        QuantifierSpec U G quant BuildUVars BuildVars ->
        forall cs facts lem args args' sub TS,
        lemmaD nil nil lem ->
        Valid PC U G facts ->
        all2 (is_well_typed (typeof_funcs funcs) (typeof_env (types := types) U) (typeof_env G)) args TS = true ->
        all2 (is_well_typed (typeof_funcs funcs) nil (Foralls lem)) args' TS = true ->
(*        allb (fun e => is_well_typed (typeof_funcs funcs) nil (Foralls lem) e tvProp) (Hyps lem) = true -> *)
        applicable unify_bound prover facts quant (length U) lem args args' = Some sub ->
        args = map (liftInstantiate quant (length U) 0 sub) args' /\
        let (lq,lh) := hash (Lhs lem) in
        let (rq,rh) := hash (Rhs lem) in
        ST.himp cs (ST_EXT.existsEach lq (fun lq => 
                       sexprD funcs preds (BuildUVars U (rev lq)) (BuildVars G (rev lq)) (*(G ++ lq)*)
                       (sheapD (applySHeap (liftInstantiate quant (length U) (length lq) sub) lh))))
                   (ST_EXT.existsEach rq (fun rq => 
                       sexprD funcs preds (BuildUVars U (rev rq)) (BuildVars G (rev rq)) (*(G ++ lq)*)
                       (sheapD (applySHeap (liftInstantiate quant (length U) (length rq) sub) rh)))).
      Proof.
        unfold applicable; intros.
        repeat match goal with
                 | [ H : match ?X with _ => _ end = _ |- _ ] => 
                   consider X; try congruence; intros
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               end.
        eapply fold_left_2_opt_unify in H4. 2: apply U.Subst_empty_WellTyped.
        Focus 3. eapply all2_impl. eassumption. intros. eapply is_well_typed_weaken with (u := Foralls lem) (g := nil).
        eassumption.
        Focus 2. rewrite all2_map_1. eapply all2_impl. eassumption. intros. 
        rewrite <- typeof_env_length. eapply openForUnification_typed. eauto.
        intuition.
        { erewrite map_ext. 
          2: intro; rewrite <- openForUnification_liftInstantiate; reflexivity.
          think. generalize (independent_well_typed _ _ H5 H8). 
          revert H9. revert H2. clear. revert args'; revert TS.
          induction args; destruct args'; destruct TS; simpl in *; intros; think; try congruence.
          inversion H9. erewrite <- IHargs; eauto. f_equal. rewrite H3. symmetry. eapply exprInstantiate_noop; eauto.
          intros. eapply H.
          eapply is_well_typed_mentionsU in H2. 2: eauto. rewrite typeof_env_length in H2. omega. }
        { consider (hash (Lhs lem)); consider (hash (Rhs lem)); intros; think.
          generalize (@checkAllInstantiated_Subst_to_env_success _ _ _ _ _
            (typeof_env_WellTyped_env U) (typeof_env_WellTyped_env G) (typeof_funcs_WellTyped_funcs funcs) sub (Foralls lem) nil).
          rewrite app_nil_r in *. intro. destruct H12. rewrite typeof_env_length; auto. auto.

          rewrite typeof_env_length in H12. generalize H0. eapply liftInstantiate_lemmaD with (quant := quant) in H0; eauto.
          intro.
          eapply implyEach_sem in H0.
          { specialize (H0 cs). 
            rewrite SH.hash_denote in H0. rewrite H10 in H0.
            rewrite SH.hash_denote with (s := Rhs lem) in H0. rewrite H8 in H0. simpl in H0.
            
            destruct H13. clear H14. unfold WellTyped_lemma in *. think.
            unfold himp in H0.
            rewrite himp_existsEach_ST_EXT_existsEach in H0.
            rewrite himp_existsEach_ST_EXT_existsEach in H0.
            etransitivity. etransitivity; [ | eapply H0 ].
            eapply ST.heq_defn. eapply ST_EXT.heq_existsEach; intros.

            rewrite applySHeap_spec. reflexivity. intros. rewrite <- rev_length with (l := G0).
            eapply liftInstantiate_spec; eauto.
            rewrite typeof_env_app. assumption.
            eapply ST.heq_defn. eapply ST_EXT.heq_existsEach; intros.
            rewrite <- applySHeap_spec. reflexivity. intros. rewrite <- rev_length with (l := G0).
            rewrite <- typeof_env_app in H17. eapply liftInstantiate_spec; eauto. }
          { destruct H13. clear H14. unfold WellTyped_lemma in H13. eapply allb_AllProvable; eauto.
            admit. (* think. revert H13. induction (Hyps lem); simpl; intros; auto; think
            rewrite andb_true_r. generalize (liftInstantiate_typed U G). *) } }
      Qed.

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

      Hint Resolve skipn_length_all : list_length.
      Hint Rewrite skipn_length_all using (eauto with list_length) : list_length.

      Lemma quantFwd_spec : forall U G (F : env types) (v : var) (t : tvar),
        is_well_typed (typeof_funcs funcs) nil (typeof_env F) (Var (types := types) v) t = true ->
        exprD funcs nil F (Var v) t =
        exprD funcs U (G ++ F) (quantFwd (length (typeof_env G)) v) t.
      Proof.
        clear. simpl. unfold lookupAs; intros. think.
        unfold typeof_env in H; rewrite map_nth_error_full in H.
        rewrite typeof_env_length.
        rewrite nth_error_app_R by omega. cutrewrite (v + length G - length G = v); [ | omega ].
        destruct (nth_error F v); auto.
      Qed.
      Lemma hintSideD_In : forall hs,
        hintSideD hs -> forall x, In x hs -> lemmaD nil nil x.
      Proof.
        clear. induction 1. inversion 1.
        intros. inversion H1; subst; auto.
      Qed.
      Lemma applySHeap_singleton : forall meta_env vars_env cs F f l,
        heq funcs preds meta_env vars_env cs
        (sheapD (applySHeap F
          {| impures := MM.mmap_add f l (MM.empty (list (expr types)))
            ; pures := nil
            ; other := nil |}))
        (sheapD 
          {| impures := MM.mmap_add f (map F l) (MM.empty (list (expr types)))
            ; pures := nil
            ; other := nil |}).
      Proof.
        clear. intros. unfold applySHeap; simpl. repeat rewrite SH.sheapD_def; simpl.
        heq_canceler. unfold MM.mmap_add. repeat rewrite MM.FACTS.empty_o.
        rewrite impuresD_Add with (f := f) (argss := map F l :: nil) (i := MM.empty _). symmetry. 
        rewrite impuresD_Add with (f := f) (argss := map F l :: nil) (i := MM.empty _). reflexivity.
        red; reflexivity. intro; eapply MM.FACTS.empty_in_iff; eassumption.
        red; reflexivity. intro; eapply MM.FACTS.empty_in_iff; eassumption.
      Qed.

      Opaque ST_EXT.existsEach.

      Lemma unfoldForwardOk : forall meta_env vars_env cs facts P Q,
        WellTyped_env (UVars P) meta_env ->
        WellTyped_env (Vars P) vars_env ->
        Valid PC meta_env vars_env facts ->
        unfoldForward unify_bound prover facts (Forward hs) P = Some Q ->
        ST.himp cs (sexprD funcs preds meta_env vars_env (sheapD (Heap P)))
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
          destruct (MF.FACTS.eq_dec f y); reflexivity. intro. apply MM.FACTS.remove_in_iff in H5. intuition congruence.
          red. intros. repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o). consider (MF.FACTS.eq_dec f y); subst; auto. 
          intro. apply MM.FACTS.remove_in_iff in H5. intuition congruence. }
        assert (exists p, nth_error preds f = Some p /\ all2 (is_well_typed (typeof_funcs funcs) UVars0 Vars0) x1 (SDomain p) = true).
        { admit. }
        destruct H5. destruct H5.

        eapply hintSideD_In in H2; eauto using ForwardOk.
        assert (length UVars0 = length meta_env).
        { unfold WellTyped_env in *. subst. rewrite map_length. auto. }
        rewrite H9 in *. 
        eapply (applicableOk (QuantifierSpec_Fwd meta_env vars_env) cs facts (*meta_env vars_env*)) in H6.
        Focus 2. eauto.
        Focus 2. eauto.
        Focus 2. unfold WellTyped_env in *. rewrite H in H8. rewrite H0 in H8. eapply H8.
        Focus 2. destruct H2. unfold WellTyped_lemma in H2. think. simpl in H12. unfold typeof_preds in H12.
          rewrite map_nth_error_full in H12. rewrite H5 in H12. eapply H12.
        { destruct H6. rewrite H3 in *. rewrite SH.hash_Func in H10. rewrite H7 in H10.
          rewrite ST_EXT.existsEach_nil in H10.
          rewrite SH.hash_denote with (s := Func f x1). rewrite SH.hash_Func.
          unfold fst, snd, SE.existsEach. rewrite app_nil_r in H10. 
          subst.
          rewrite applySHeap_singleton in H10. simpl in H10. simpl. rewrite H10. clear H10.
          rewrite ST_EXT.heq_pushIn. rewrite rw_skipn_app; eauto with list_length.

          rewrite ST_EXT.existsEach_rev. eapply ST.heq_defn. eapply ST_EXT.heq_existsEach; intros.
          rewrite <- star_SHeap_denote. simpl. apply ST.heq_star_frame. 
          { admit.  (** This requires weakening **) }
          { rewrite rev_involutive. unfold WellTyped_env in *. subst. repeat rewrite map_length.
            cutrewrite (length v = length (rev G)). reflexivity.
            rewrite <- rev_length. rewrite <- H6. rewrite map_length. rewrite rev_length. reflexivity. } }
      Qed.
      
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

      Theorem forwardOk : forall cs bound facts P Q,
        forward bound facts P = Q ->
        forall meta_env vars_env,
        WellTyped_env (UVars P) meta_env -> (** meta_env instantiates the uvars **)
        WellTyped_env (Vars P) vars_env ->
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
            rewrite ST_EXT.existsEach_app; intros.
            eapply ST_EXT.himp_existsEach. intros.
            rewrite IHbound; try solve [  repeat match goal with 
                                                   | [ H : _ = _ |- _ ] => rewrite H
                                                 end; auto ].
            rewrite H5. rewrite rw_skipn_app.
            apply ST_EXT.himp_existsEach; intros.
            repeat (rewrite app_nil_r || rewrite app_ass). reflexivity.
            rewrite H3. repeat rewrite app_length. subst. rewrite H1. repeat rewrite map_length. reflexivity.
 
            red. rewrite map_app.
            repeat match goal with
                     | [ H : _ = _ |- _ ] => rewrite H
                   end. f_equal; auto. 
            rewrite <- app_nil_r with (l := meta_env); eapply Valid_weaken; eauto. }
          { subst. erewrite skipn_length_all by eauto with list_length.
            rewrite ST_EXT.existsEach_nil. rewrite app_nil_r. reflexivity. } }
      Qed.

      Theorem backwardOk : forall cs bound facts P Q meta_env vars_env,
        backward bound facts P = Q ->
        WellTyped_env (UVars P) meta_env -> (** meta_env instantiates the uvars **)
        WellTyped_env (Vars P) vars_env ->
        Valid PC meta_env vars_env facts ->
        ST.himp cs (ST_EXT.existsEach (skipn (length meta_env) Q.(UVars)) (fun meta_ext : env types => 
                      (sexprD funcs preds (meta_env ++ meta_ext) vars_env (sheapD (Heap Q)))))
                   (sexprD funcs preds meta_env vars_env (sheapD (Heap P))).
      Proof.
        induction bound; simpl; intros.
        { subst. cutrewrite (skipn (length meta_env) (UVars Q) = nil). rewrite ST_EXT.existsEach_nil. 
          rewrite app_nil_r. reflexivity. eauto with list_length. }
        { consider (unfoldBackward unify_bound prover facts (Backward hs) P); intros.
          { admit. }
          { subst. cutrewrite (skipn (length meta_env) (UVars Q) = nil). rewrite ST_EXT.existsEach_nil. 
          rewrite app_nil_r. reflexivity. eauto with list_length. } }
      Qed.

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
        || (constructor; [ split; [ reflexivity | exact P1 ] | prove P2 ])
      | _ => constructor; [ split; [ reflexivity | exact Ps ] | constructor ]
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

