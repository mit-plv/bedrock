Require Import IL SepIL.
Require Import Word Memory.
Import List.
Require Import DepList EqdepClass.
Require Import PropX.
Require Import Expr SepExpr SepCancel.
Require Import Prover ILEnv.
Require Import Tactics Reflection.
Require Import TacPackIL.
Require ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

(*TIME
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.  
Add ML Path "/usr/local/lib/coq/user-contrib/". 
Declare ML Module "Timing_plugin".
*)

Module U := ExprUnify.UNIFIER.
Module CANCEL := SepCancel.Make U SepIL.SH.

Section existsSubst.
  Variable types : list type.
  Variable funcs : functions types.
  Variable meta_base : env types.
  Variable var_env : env types.
  Variable sub : U.Subst types.
 
  Definition ExistsSubstNone (_ : list { t : tvar & option (tvarD types t) }) (_ : tvar) (_ : expr types) := 
    False.
  Definition ExistsSubstSome (_ : list { t : tvar & option (tvarD types t) }) (_ : expr types) := 
    False. 

  Fixpoint existsSubst (from : nat) (vals : list { t : tvar & option (tvarD types t) }) (ret : env types -> Prop) : Prop :=
    match vals with
      | nil => ret nil
      | existT t None :: vals =>
        match U.Subst_lookup from sub with
          | None => exists v : tvarD types t, existsSubst (S from) vals (fun env => ret (existT (tvarD types) t v :: env))
          | Some v =>
            match exprD funcs meta_base var_env v t with
              | None => ExistsSubstNone vals t v
              | Some v => existsSubst (S from) vals (fun env => ret (existT (tvarD types) t v :: env))
            end
        end
      | existT t (Some v) :: vals =>
        match U.Subst_lookup from sub with
          | None => existsSubst (S from) vals (fun env => ret (existT (tvarD types) t v :: env))
          | Some v' =>
            match exprD funcs meta_base var_env v' t with
              | None => ExistsSubstSome vals v'
              | Some v' => 
                existsSubst (S from) vals (fun env => v = v' /\ ret (existT (tvarD types) t v' :: env))
            end
        end
    end.
End existsSubst.

Section typed.
  Variable types : list type.
  Variable funcs : functions types. 
  Variables uenv venv : env types.
  Variable subst : U.Subst types.

  Fixpoint Subst_equations_to (from : nat) (ls : Expr.env types) : Prop :=
    match ls with
      | nil => True
      | l :: ls =>
        match U.Subst_lookup from subst with
          | None => True
          | Some e => match exprD funcs uenv venv e (projT1 l) with
                        | None => False
                        | Some v => projT2 l = v
                      end
        end /\ Subst_equations_to (S from) ls 
    end.
End typed.

Fixpoint consistent {ts} (vals : list { x : tvar & option (tvarD ts x) }) (e : list { x : tvar & tvarD ts x }) : Prop :=
  match vals , e with
    | nil , nil => True
    | existT t None :: vals , existT t' _ :: e =>
      t = t' /\ @consistent _ vals e
    | existT t (Some v) :: vals , existT t' v' :: e =>
      match equiv_dec t t' return Prop with
        | left pf => 
          v' = match (pf : t = t') in _ = t return tvarD ts t with
                 | refl_equal => v
               end /\ @consistent _ vals e
        | right _ => False
      end
    | _ , _ => False
  end.

Lemma existsSubst_sem : forall ts (funcs : functions ts) vals sub meta_base vars_env from ret,
  existsSubst funcs meta_base vars_env sub from vals ret <->
  existsEach (map (@projT1 _ _) vals) (fun meta_env =>
    consistent vals meta_env /\ Subst_equations_to funcs meta_base vars_env sub from meta_env /\ ret meta_env).
Proof.
  induction vals; intros; simpl in *.
  { intuition. }
  { destruct a. destruct o;
    repeat match goal with
             | |- context [ match U.Subst_lookup ?A ?B with _ => _ end ] =>
               consider (U.Subst_lookup A B); intros; simpl in *
             | |- context [ match exprD ?A ?B ?C ?D ?E with _ => _ end ] =>
               consider (exprD A B C D E); intros; simpl in *
             | |- _ => rewrite EquivDec_refl_left in *
             | |- _ <-> _ => split; intro
             | H : existsEach _ _ |- _ => apply existsEach_sem in H
             | |- existsEach _ _ => apply existsEach_sem
             | H : existsSubst _ _ _ _ _ _ _ |- _ => apply IHvals in H
             | |- existsSubst _ _ _ _ _ _ _ => apply IHvals
             | H : exists x, _ |- exists y, _ =>
               let f := fresh in destruct H as [ f ? ] ; exists f
             | H : tvarD ?X ?Y |- exists y : tvarD ?X ?Y, _ =>
               exists H
             | H : exists y, _ |- _ => destruct H
           end; intuition; subst; auto. subst; auto. }
Qed.

Lemma ex_iff : forall T (P P' : T -> Prop),
  (forall x, P x <-> P' x) ->
  ((exists x, P x) <-> (exists x, P' x)).
Proof. split; intuition; destruct H0 as [ x ? ]; exists x; firstorder. Qed.

Lemma existsSubst_app : forall ts (fs : functions ts) meta_base vars_base sub a b from ret,
  existsSubst fs meta_base vars_base sub from (a ++ b) ret <->
  existsSubst fs meta_base vars_base sub from a (fun a_env =>
    existsSubst fs meta_base vars_base sub (from + length a) b (fun b_env => ret (a_env ++ b_env))).
Proof.
  induction a; intros; simpl in *.
  { rewrite Plus.plus_0_r. intuition. }
  { destruct a; destruct o;
    repeat match goal with
             | |- context [ match U.Subst_lookup ?A ?B with _ => _ end ] =>
               consider (U.Subst_lookup A B); intros; simpl in *
             | |- context [ match exprD ?A ?B ?C ?D ?E with _ => _ end ] =>
               consider (exprD A B C D E); intros; simpl in *
             | |- _ <-> _ => apply ex_iff; intros
             | |- _ => rewrite IHa
             | |- _ => rewrite <- plus_n_Sm
           end; try solve [ intuition ]; clear IHa; split; intros;
    repeat match goal with
             | H : existsSubst _ _ _ _ _ _ _ |- _ => apply existsSubst_sem in H
             | |- existsSubst _ _ _ _ _ _ _ => apply existsSubst_sem 
             | H : existsEach _ _ |- _ => apply existsEach_sem in H
             | |- existsEach _ _ => apply existsEach_sem 
             | H : exists x, _ |- exists y, _ =>
               let f := fresh in destruct H as [ f ? ] ; exists f
             | |- _ => progress intuition
           end.
    destruct H6. intuition. }
Qed.     

Lemma AllProvable_impl_AllProvable : forall ts (funcs : functions ts) U G P ps,
  AllProvable funcs U G ps ->
  AllProvable_impl funcs U G P ps ->
  P.
Proof. clear. induction ps; simpl; intros; eauto. intuition. Qed.    

Section canceller.
  Variable ts : list type.
  Let types := Env.repr BedrockCoreEnv.core ts.
  Variable funcs : functions types.
  Variable preds : SEP.predicates types BedrockCoreEnv.pc BedrockCoreEnv.st.
  Variable algos : ILAlgoTypes.AllAlgos ts.

  Record CancellerResult : Type :=
  { AllExt : variables
  ; ExExt  : variables
  ; Lhs    : SH.SHeap types BedrockCoreEnv.pc BedrockCoreEnv.st
  ; Rhs    : SH.SHeap types BedrockCoreEnv.pc BedrockCoreEnv.st
  ; Subst  : U.Subst types
  }.

  Definition canceller (uvars : list tvar) (hyps : Expr.exprs types)
    (lhs rhs : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st) : CancellerResult :=
    let prover := 
      match ILAlgoTypes.Prover algos with
        | None => provers.ReflexivityProver.reflexivityProver
        | Some p => p
      end
    in
    let hints :=
      match ILAlgoTypes.Hints algos with
        | None => UNF.default_hintsPayload _ _ _ 
        | Some h => h
      end
    in
    let (ql, lhs) := SH.hash lhs in
    let facts := Summarize prover (map (liftExpr 0 0 0 (length ql)) hyps ++ SH.pures lhs) in
    let pre :=
      {| UNF.Vars  := rev ql
       ; UNF.UVars := uvars
       ; UNF.Heap  := lhs
      |}
    in
    match UNF.forward hints prover 10 facts pre with
      | {| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := lhs |} =>
        let (qr, rhs) := SH.hash rhs in
        let rhs := 
          UNF.HEAP_FACTS.sheapSubstU 0 (length qr) (length uvars') rhs
        in
        let post :=
          {| UNF.Vars  := vars'
           ; UNF.UVars := uvars' ++ rev qr
           ; UNF.Heap  := rhs
          |}
        in
        match UNF.backward hints prover 10 facts post with
          | {| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := rhs |} =>
            let new_vars  := vars' in
            let new_uvars := skipn (length uvars) uvars' in
            let bound := length uvars' in
            match CANCEL.sepCancel preds prover bound facts lhs rhs with
              | (l,r,s) =>
                {| AllExt := new_vars
                 ; ExExt  := new_uvars
                 ; Lhs    := l
                 ; Rhs    := r
                 ; Subst  := s
                 |}
            end
        end
    end.

  Lemma AllProvable_and_sem : forall U G P Ps,
    AllProvable_and funcs U G P Ps <-> (AllProvable funcs U G Ps /\ P).
  Proof. induction Ps; simpl; intros; intuition auto. Qed.
  Lemma app_inj_length : forall T (a b c d : list T),
    a ++ b = c ++ d ->
    length a = length c ->
    a = c /\ b = d.
  Proof.
    induction a; destruct c; simpl; intros; think; try solve [ intuition ].
    inversion H; subst.  eapply IHa in H3. intuition; subst; auto. omega.
  Qed.
  Lemma WellTyped_env_app : forall ts a b c d,
    WellTyped_env a c ->
    WellTyped_env b d ->
    WellTyped_env (types := ts) (a ++ b) (c ++ d).
  Proof. clear.
    intros. unfold WellTyped_env in *. unfold typeof_env in *. subst. 
    rewrite map_app. reflexivity.
  Qed.
  Ltac t_list_length := repeat (rewrite typeof_env_length || rewrite rev_length || rewrite map_length || rewrite app_length).
  Hint Extern 1 (_ = _) => t_list_length; auto : list_length.

  Ltac env_resolution :=
    repeat (rewrite typeof_env_app || unfold typeof_env || rewrite map_app || rewrite map_rev || (f_equal; []) || assumption).

  Lemma consistent_app : forall ts a b c,
    consistent (ts := ts) (a ++ b) c ->
    consistent a (firstn (length a) c) /\ consistent b (skipn (length a) c).
  Proof. clear.
    induction a; simpl; intros; auto.
    destruct a. destruct o. destruct c; try contradiction. destruct s. destruct (equiv_dec x x0); try contradiction.
    destruct H. eapply IHa in H0. intuition.
    destruct c; try contradiction. destruct s. destruct H. apply IHa in H0. intuition.
  Qed.
  Lemma consistent_Some : forall ts a c,
    consistent (ts := ts) (map (fun x => existT _ (projT1 x) (Some (projT2 x))) a) c ->
    a = c.
  Proof.
    induction a; destruct c; simpl; intros; try contradiction; auto.
    destruct s. destruct a; simpl in *. destruct (equiv_dec x0 x); try contradiction.
    unfold equiv in e. intuition; subst. f_equal; eauto.
  Qed.
  Lemma skipn_length : forall T a (b : list T),
    length (skipn a b) = length b - a.
  Proof. induction a; destruct b; simpl; intros; auto. Qed.

  Lemma ApplyCancelSep_with_eq' : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : env types) (hyps : Expr.exprs types),
    Expr.AllProvable funcs meta_env nil hyps ->
    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st) res cs,
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true),
    canceller (typeof_env meta_env) hyps l r = res ->
    match res with
      | {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          (existsSubst funcs meta_env var_env subst 0 
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
              Expr.AllProvable_impl funcs meta_env var_env
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) 
            (SH.pures lhs')) ))
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof.
    Opaque UNF.backward UNF.forward Env.repr.
    intros. unfold canceller in *.
    assert (PC : ProverT_correct
              match ILAlgoTypes.Prover algos with
              | Some p => p
              | None => ReflexivityProver.reflexivityProver
              end funcs).
    { generalize (ILAlgoTypes.Acorrect_Prover algos_correct).
      destruct (ILAlgoTypes.Prover algos); intros; auto.
      apply ReflexivityProver.reflexivityProver_correct. }
    generalize dependent (match ILAlgoTypes.Prover algos with
                            | Some p => p
                            | None => ReflexivityProver.reflexivityProver
                          end).
    match goal with
      | [ |- context [ ?X ] ] =>
        match X with 
          | match ILAlgoTypes.Hints _ with _ => _ end =>
            assert (HC : UNF.hintsSoundness funcs preds X); [ | generalize dependent X ]
        end
    end.
    { generalize (ILAlgoTypes.Acorrect_Hints algos_correct).     
      destruct (ILAlgoTypes.Hints algos); auto using UNF.hintsSoundness_default. }
    intros h HC p ? PC.
    consider (SH.hash l); intros.
    rewrite SH.hash_denote. rewrite H0; clear H0; simpl.
    consider (SH.hash r); intros.
    rewrite SH.hash_denote with (s := r). rewrite H0; simpl.
    rewrite UNF.himp_existsEach_ST_EXT_existsEach.
    rewrite UNF.ST_EXT.himp_existsEach_p; [ reflexivity | intros ].
    rewrite app_nil_r.
    apply CANCEL.HEAP_FACTS.himp_pull_pures; intro.
    match goal with 
      | [ H : context [ Summarize ?P ?ps ] |- _ ] =>
        assert (Valid PC meta_env (rev G) (Summarize P ps)); [ | generalize dependent (Summarize P ps); intros ]
    end.
    { eapply Summarize_correct.
      apply AllProvable_app; auto.
      revert H; clear - H3. induction hyps; simpl; intros; auto.
      intuition. clear - H0 H3. unfold Provable in *.
      generalize (liftExpr_ext funcs meta_env nil nil nil (rev G) nil a tvProp); simpl.
      rewrite app_nil_r. rewrite rev_length. subst. rewrite map_length.
      intro. rewrite H in *. auto. }
    match goal with
      | [ H : match ?X with _ => _ end = _ |- _ ] => consider X
    end; intros.
    apply CANCEL.SEP_FACTS.himp_WellTyped_sexpr; intro.

    (** Forward **)
    destruct (UNF.forwardLength _ _ _ _ _ H2).
    assert (SH.WellTyped_sheap (typeof_funcs funcs) (UNF.SE.typeof_preds preds) (typeof_env meta_env) (rev v) s = true).
    { rewrite SH.WellTyped_sheap_WellTyped_sexpr. rewrite <- H3. rewrite <- map_rev. apply H7. }
    generalize (@UNF.forward_WellTyped _ _ _ _ _ _ _ HC _ _ _ _ H2 H9); intro.
    simpl in *.
    assert (WellTyped_env (rev v) (rev G)).
    { unfold WellTyped_env. subst. rewrite <- map_rev. auto. }
    eapply UNF.forwardOk  with (cs := cs) in H2; simpl; eauto using typeof_env_WellTyped_env.
    simpl in H2. etransitivity; [ eapply H2 | clear H11; simpl in * ].
    rewrite UNF.ST_EXT.himp_existsEach_p; [ reflexivity | intros ].
    destruct H8.
    (** NOTE: I can't shift s0 around until I can witness the existential **)
    
    
    (** Open up everything **)
    consider (UNF.backward h p 10 f
           {| UNF.Vars := Vars
            ; UNF.UVars := UVars ++ rev v0
            ; UNF.Heap := UNF.HEAP_FACTS.sheapSubstU 0 (length v0) (length UVars) s0 |}); intros.
    destruct (UNF.backwardLength _ _ _ _ _ H6); simpl in *.
    consider (CANCEL.sepCancel preds p (length UVars0) f Heap Heap0); intros.
    destruct p0. intuition; subst.
    rewrite ListFacts.rw_skipn_app in H11 by auto with list_length. 

    eapply forallEach_sem with (env := rev G ++ G0) in H1; [ | solve [ env_resolution ] ]. 
    
    apply existsSubst_sem in H1. apply existsEach_sem in H1.
    destruct H1. intuition.
    assert (meta_env = firstn (length meta_env) x1 /\
            typeof_env (skipn (length (rev v0)) (skipn (length meta_env) x1)) = x0 /\ 
            typeof_env (firstn (length (rev v0)) (skipn (length meta_env) x1)) = rev v0).
    { clear - H3 H1.
      generalize (typeof_env_length x1). rewrite H3; intros.
      rewrite <- firstn_skipn with (n := length meta_env) (l := x1) in H3.
      repeat (rewrite map_app in *  || rewrite map_map in * || rewrite map_id in * || rewrite app_ass in *
        || rewrite ListFacts.rw_skipn_app in * by eauto || rewrite typeof_env_app in *).
      simpl in *. rewrite typeof_env_app in *. eapply app_inj_length in H3.
      Focus 2. revert H. t_list_length. rewrite firstn_length. intro. rewrite min_l; omega.
      destruct H3.
      rewrite <- firstn_skipn with (n := length (rev v0)) (l := skipn (length meta_env) x1) in H2.
      rewrite typeof_env_app in *. 
      eapply app_inj_length in H2. destruct H2. intuition.
      { eapply consistent_app in H1. destruct H1; clear - H1.
        revert H1. t_list_length. intros.
        eapply consistent_Some in H1. auto. }
      revert H. t_list_length. intro. rewrite firstn_length; rewrite min_l; auto.
      rewrite skipn_length. omega. }
    intuition. clear H3 H1.
    eapply (@CANCEL.HEAP_FACTS.himp_pull_pures types _ _ funcs preds cs meta_env (rev G ++ G0) Heap). intro.
    eapply AllProvable_impl_AllProvable in H14.
    Focus 2. eapply CANCEL.sepCancel_PuresPrem; eauto.
    rewrite <- firstn_skipn with (n := length meta_env) (l := x1).
    rewrite <- app_nil_r with (l := rev G ++ G0). eapply AllProvable_weaken. rewrite <- H15. solve [ auto ].

    eapply AllProvable_and_sem in H14. destruct H14.
    rewrite app_ass in *.

    assert (SH.WellTyped_sheap (typeof_funcs funcs) (UNF.SE.typeof_preds preds)
     (typeof_env meta_env ++ rev v0)
     (rev (map (projT1 (P:=tvarD types)) G) ++ x)
     (UNF.HEAP_FACTS.sheapSubstU 0 (length v0) (length (typeof_env meta_env))
        s0) = true).
    { rewrite <- SH.WellTyped_sheap_WellTyped_sexpr in H7.
      generalize (@UNF.HEAP_FACTS.sheapSubstU_wt types BedrockCoreEnv.pc BedrockCoreEnv.st (typeof_funcs funcs) (UNF.SE.typeof_preds preds) (typeof_env meta_env) nil (rev v0) nil s0); simpl.   
      rewrite app_nil_r. intro XX.
      rewrite SH.WellTyped_hash in WTR. rewrite H0 in WTR. simpl in WTR. rewrite app_nil_r in WTR.
      apply XX in WTR. clear XX.
      eapply SH.WellTyped_sheap_weaken with (tU' := nil) (tG := nil) (tG' := (rev (map (projT1 (P:=tvarD types)) G) ++ x)) in WTR. 
      simpl in WTR. rewrite app_nil_r in WTR.  
      rewrite Plus.plus_0_r in *. rewrite rev_length in WTR. apply WTR. }
    
    generalize (@UNF.backward_WellTyped _ _ _ _ _ _ _ HC _ _ _ _ H6 H16); simpl.
    eapply UNF.backwardOk with (cs := cs) in H6; simpl in *.
    2: eassumption.
    2: solve [ rewrite <- H17; eapply WellTyped_env_app; eauto using typeof_env_WellTyped_env ].
    Focus 2.
    rewrite <- map_rev.
    eapply WellTyped_env_app. eapply typeof_env_WellTyped_env.
    instantiate (1 := G0). symmetry. apply H11. 
    2: eassumption.
    2: solve [ eapply Valid_weaken; eassumption ].
    intro.

    (** **)
    rewrite UNF.himp_existsEach_ST_EXT_existsEach.
    eapply UNF.ST_EXT.himp_existsEach_c. exists (rev (firstn (length (rev v0)) (skipn (length meta_env) x1))); split.
    { rewrite map_rev. unfold typeof_env in H17. rewrite H17. apply rev_involutive. }
    rewrite rev_involutive.
    
    (** In order to call the canceller, they must have the same environments. **)
    assert (SH.SE.ST.heq cs 
              (SH.SE.sexprD funcs preds meta_env (rev G ++ G0) (SH.sheapD Heap))
              (SH.SE.sexprD funcs preds x1 (rev G ++ G0) (SH.sheapD Heap))).
    { rewrite <- firstn_skipn with (l := x1) (n := length meta_env).
      rewrite <- H15.
      generalize (@CANCEL.SEP_FACTS.sexprD_weaken_wt types _ _ funcs preds cs meta_env (skipn (length meta_env) x1) nil 
        (SH.sheapD Heap) (rev G ++ G0)).
      rewrite app_nil_r. intro XX; apply XX; clear XX.
      rewrite <- SH.WellTyped_sheap_WellTyped_sexpr. rewrite <- H10. f_equal.
      rewrite typeof_env_app. f_equal. rewrite <- map_rev. reflexivity.
      rewrite <- H11. reflexivity. }
    etransitivity; [ eapply H19 | clear H19 ].
(*
    assert (SH.SE.ST.heq cs 
              (SH.SE.sexprD funcs preds x1 (rev G ++ G0) (SH.sheapD (UNF.HEAP_FACTS.sheapSubstU 0 (length v0)
                       (length (typeof_env meta_env)) s0)))
              (UNF.SE.sexprD funcs preds meta_env
                (firstn (length (rev v0)) (skipn (length meta_env) x1) ++ nil)
                (SH.sheapD s0))).
    { generalize (@UNF.HEAP_FACTS.sheapSubstU_sheapD types _ _ funcs preds cs 
        meta_env nil (firstn (length (rev v0)) (skipn (length meta_env) x1)) nil s0).
      simpl. repeat rewrite app_nil_r. intros XX; rewrite XX; clear XX.
      generalize (@CANCEL.SEP_FACTS.sexprD_weaken_wt types _ _ funcs preds cs
        (meta_env ++ firstn (length (rev v0)) (skipn (length meta_env) x1))
        (skipn (length (rev v0)) (skipn (length meta_env) x1)) (rev G ++ G0)
          (SH.sheapD (UNF.HEAP_FACTS.sheapSubstU 0
              (length (firstn (length (rev v0)) (skipn (length meta_env) x1)) +
               0) (length meta_env) s0)) nil).
      simpl. t_list_length.
      intro XX; rewrite XX; clear XX.
      rewrite H15. rewrite app_ass. 
      cutrewrite (length (firstn (length meta_env) x1) = length meta_env).
      repeat rewrite firstn_skipn.
      cutrewrite (length (firstn (length v0) (skipn (length meta_env) x1)) + 0 = length v0).
      reflexivity.
      rewrite Plus.plus_0_r. rewrite <- rev_length with (l := v0). 
      rewrite <- H17 at 2. t_list_length. reflexivity.
      rewrite <- H15. reflexivity.
      rewrite <- SH.WellTyped_sheap_WellTyped_sexpr.
      rewrite SH.WellTyped_hash in WTR.
      rewrite SH.WellTyped_sheap_WellTyped_sexpr in WTR. rewrite H0 in *. simpl in WTR.
      clear - WTR H15 H12 H17 H11.
      rewrite <- SH.WellTyped_sheap_WellTyped_sexpr in WTR.
      generalize (@sheapSubstU_WellTyped_eq types BedrockCoreEnv.pc BedrockCoreEnv.st (typeof_funcs funcs) (SEP.typeof_preds preds)
        (typeof_env meta_env) nil (rev v0) nil s0). simpl. t_list_length. rewrite app_nil_r in *.
      intro XX; rewrite XX in WTR; clear XX.
      rewrite <- WTR. rewrite <- H17. t_list_length. rewrite typeof_env_app. repeat rewrite Plus.plus_0_r.
      f_equal. f_equal. rewrite <- rev_length with (l := v0). rewrite <- H17 at 2.
      t_list_length. reflexivity. }
*)
      Lemma sheapSubstU_WellTyped_eq : forall types pcT stT tf tp tu tg tg' tg'' s,
        SH.WellTyped_sheap (types := types) (pcType := pcT) (stateType := stT) tf tp tu (tg ++ tg' ++ tg'') s = 
        SH.WellTyped_sheap tf tp (tu ++ tg') (tg ++ tg'') (UNF.HEAP_FACTS.sheapSubstU (length tg) (length tg' + length tg) (length tu) s).
      Admitted. 

    assert (SH.SE.ST.heq cs 
              (SH.SE.sexprD funcs preds (meta_env ++ firstn (length (rev v0)) (skipn (length meta_env) x1)) (rev G ++ G0) (SH.sheapD (UNF.HEAP_FACTS.sheapSubstU 0 (length v0)
                       (length (typeof_env meta_env)) s0)))
              (UNF.SE.sexprD funcs preds meta_env
                (firstn (length (rev v0)) (skipn (length meta_env) x1) ++ nil)
                (SH.sheapD s0))).
    { generalize (@UNF.HEAP_FACTS.sheapSubstU_sheapD types _ _ funcs preds cs 
        meta_env nil (firstn (length (rev v0)) (skipn (length meta_env) x1)) nil s0).
      simpl. repeat rewrite app_nil_r. intros XX; rewrite XX; clear XX.
      generalize (@CANCEL.SEP_FACTS.sexprD_weaken_wt types _ _ funcs preds cs
        (meta_env ++ firstn (length (rev v0)) (skipn (length meta_env) x1))
        nil (rev G ++ G0)
          (SH.sheapD (UNF.HEAP_FACTS.sheapSubstU 0
              (length (firstn (length (rev v0)) (skipn (length meta_env) x1)) +
               0) (length meta_env) s0)) nil).
      simpl. t_list_length.
      intro XX; rewrite XX; clear XX.
      rewrite H15. rewrite app_ass. 
      cutrewrite (length (firstn (length meta_env) x1) = length meta_env).
      rewrite app_nil_r.
      cutrewrite (length (firstn (length v0) (skipn (length meta_env) x1)) + 0 = length v0).
      reflexivity.
      rewrite Plus.plus_0_r. rewrite <- rev_length with (l := v0). 
      rewrite <- H17 at 2. t_list_length. reflexivity.
      rewrite <- H15. reflexivity.
      rewrite <- SH.WellTyped_sheap_WellTyped_sexpr.
      rewrite SH.WellTyped_hash in WTR.
      rewrite SH.WellTyped_sheap_WellTyped_sexpr in WTR. rewrite H0 in *. simpl in WTR.
      clear - WTR H15 H12 H17 H11.
      rewrite <- SH.WellTyped_sheap_WellTyped_sexpr in WTR.
      generalize (@sheapSubstU_WellTyped_eq types BedrockCoreEnv.pc BedrockCoreEnv.st (typeof_funcs funcs) (SEP.typeof_preds preds)
        (typeof_env meta_env) nil (rev v0) nil s0). simpl. t_list_length. rewrite app_nil_r in *.
      intro XX; rewrite XX in WTR; clear XX.
      rewrite <- WTR. rewrite <- H17. t_list_length. rewrite typeof_env_app. repeat rewrite Plus.plus_0_r.
      f_equal. f_equal. rewrite <- rev_length with (l := v0). rewrite <- H17 at 2.
      t_list_length. reflexivity. }
    rewrite <- H19; clear H19.
    revert H6. t_list_length.
    intro H6. etransitivity; [ clear H6 | eapply H6 ].

    
    (** witness the conclusion **)
    eapply UNF.ST_EXT.himp_existsEach_c. 
    exists (skipn (length (rev v0)) (skipn (length meta_env) x1)). split. 
    { t_list_length. rewrite firstn_length; rewrite skipn_length. rewrite <- app_ass. rewrite ListFacts.rw_skipn_app.
      rewrite <- H12. t_list_length. reflexivity.
      env_resolution. t_list_length. f_equal. rewrite min_l; auto.
      clear - H17 H15 H12.
      assert (x1 = firstn (length meta_env) x1 ++ (firstn (length (rev v0)) (skipn (length meta_env) x1)) ++ 
        (skipn (length (rev v0)) (skipn (length meta_env) x1))).
      repeat rewrite firstn_skipn. reflexivity. 
      generalize dependent (firstn (length meta_env) x1).
      generalize dependent (skipn (length (rev v0)) (skipn (length meta_env) x1)).
      generalize dependent (firstn (length (rev v0)) (skipn (length meta_env) x1)).
      intros. subst. rewrite <- rev_length. rewrite <- H17. t_list_length. omega. }
    rewrite app_ass. rewrite H15 at 1.
    t_list_length. repeat rewrite firstn_skipn.
    clear H2. 

    (** Finally the cancellation **)
    eapply CANCEL.sepCancel_correct with (cs := cs) (funcs := funcs) (U := x1) (G := rev G ++ G0) in H13.
    eapply H13.
    { admit. (** welltyped_subst **) }
    { eapply SH.WellTyped_sheap_weaken with (tG' := nil) (tU' := typeof_env (skipn (length meta_env) x1)) in H10.
      rewrite H15 in H10 at 1. rewrite <- typeof_env_app in H10. rewrite firstn_skipn in H10.
      rewrite app_nil_r in H10. rewrite <- H10. f_equal.
      rewrite typeof_env_app. rewrite typeof_env_rev. f_equal. apply H11. }
    { rewrite <- H18. f_equal.
      rewrite H15. rewrite <- H17. rewrite <- H12. t_list_length. 
      repeat rewrite <- typeof_env_app. repeat rewrite firstn_skipn. reflexivity.
      rewrite typeof_env_app. f_equal. rewrite typeof_env_rev. reflexivity. apply H11. }
    { instantiate (1 := PC). eapply Valid_weaken with (ue := skipn (length meta_env) x1) (ge := G0) in H5.
      rewrite <- firstn_skipn with (n := length meta_env) (l := x1). rewrite <- H15. assumption. }
    { admit. (** TODO: I need to know something about the pures **) }
    { admit. (** subst_equations from Subst_equations_to **) }
  Qed.

  Lemma ApplyCancelSep_with_eq : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),

    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st) res,
    Expr.AllProvable funcs meta_env nil hyps ->
    canceller (typeof_env meta_env) hyps l r = res ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,
    match res with
      | {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
            (existsSubst funcs meta_env var_env subst 0 
              (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
               map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
              (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof. intros. eapply ApplyCancelSep_with_eq'; eauto. Qed.

  Lemma ApplyCancelSep : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),
    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st),
      Expr.AllProvable funcs meta_env nil hyps ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,
    match canceller (typeof_env meta_env) hyps l r with
      | {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach ((*rev*) new_vars) (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
            (existsSubst funcs meta_env var_env subst 0 
              (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
               map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
              (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof. intros. eapply ApplyCancelSep_with_eq; eauto. Qed.

End canceller.

Lemma interp_interp_himp : forall cs P Q stn_st,
  interp cs (![ P ] stn_st) ->
  (himp cs P Q) ->
  interp cs (![ Q ] stn_st).
Proof.
  unfold himp. intros. destruct stn_st.
  rewrite sepFormula_eq in *. unfold sepFormula_def in *. simpl in *.
  eapply Imply_E; eauto. 
Qed.

Theorem change_Imply_himp : forall (specs : codeSpec W (settings * state)) p q s,
  himp specs p q
  -> interp specs (![p] s ---> ![q] s)%PropX.
Proof.
  rewrite sepFormula_eq.
  unfold himp, sepFormula_def.
  eauto.
Qed.

Lemma ignore_regs : forall p specs stn st rs,
  interp specs (![ p ] (stn, st))
  -> interp specs (![ p ] (stn, {| Regs := rs; Mem := Mem st |})).
Proof.
  rewrite sepFormula_eq; auto.
Qed.

Ltac change_to_himp := try apply ignore_regs;
  match goal with
    | [ H : interp ?specs (![ _ ] ?X)
      |- interp ?specs (![ _ ] ?X) ] =>
      eapply (@interp_interp_himp _ _ _ _ H)
    | [ |- _ ===> _ ] => hnf; intro
    | _ => apply change_Imply_himp
  end.

Module SEP_REIFY := ReifySepExpr.ReifySepExpr SEP.

(** The parameters are the following.
 ** - [isConst] is an ltac [* -> bool]
 ** - [ext] is a [TypedPackage .. .. .. .. ..]
 ** - [simplifier] is an ltac that simplifies the goal after the cancelation, it is passed
 **   constr:(tt).
 **)
Ltac sep_canceler isConst ext simplifier :=
(*TIME  start_timer "sep_canceler:change_to_himp" ; *)
  (try change_to_himp) ;
(*TIME  stop_timer "sep_canceler:change_to_himp" ; *)
(*TIME  start_timer "sep_canceler:init" ; *)
  let ext' := 
    match ext with
      | tt => eval cbv delta [ ILAlgoTypes.BedrockPackage.bedrock_package ] in ILAlgoTypes.BedrockPackage.bedrock_package
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
    end
  in
  let shouldReflect P :=
    match P with
      | evalInstrs _ _ _ = _ => false
      | Structured.evalCond _ _ _ _ _ = _ => false
      | @PropX.interp _ _ _ _ => false
      | @PropX.valid _ _ _ _ _ => false
      | @eq ?X _ _ => 
        match X with
          | context [ PropX.PropX ] => false
          | context [ PropX.spec ] => false
        end
      | forall x, _ => false
      | exists x, _ => false
      | _ => true
    end
  in
  let reduce_repr ls :=
    match ls with
      | _ => 
        eval cbv beta iota zeta delta [
          ext
          ILAlgoTypes.PACK.applyTypes
          ILAlgoTypes.PACK.applyFuncs 
          ILAlgoTypes.PACK.applyPreds
          ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds

          Env.repr Env.listToRepr Env.repr_combine Env.listOptToRepr Env.nil_Repr
          BedrockCoreEnv.core 
          ILAlgoTypes.Env
          tl map
          bedrock_types_r bedrock_funcs_r
        ] in ls
      | _ => 
        eval cbv beta iota zeta delta [
          ILAlgoTypes.PACK.applyTypes
          ILAlgoTypes.PACK.applyFuncs 
          ILAlgoTypes.PACK.applyPreds
          ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
          
          Env.repr Env.listToRepr Env.repr_combine Env.listOptToRepr Env.nil_Repr
          BedrockCoreEnv.core
          ILAlgoTypes.Env
          tl map
          bedrock_types_r bedrock_funcs_r
        ] in ls
    end
  in
  match goal with 
    | [ |- himp ?cs ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
(*TIME      start_timer "sep_canceler:init"; *)
(*TIME      start_timer "sep_canceler:gather_props" ; *)
      let all_props := 
        ReifyExpr.collect_props ltac:(SEP_REIFY.reflectable shouldReflect)
      in
      let pures := ReifyExpr.props_types all_props in
(*TIME      stop_timer "sep_canceler:gather_props" ; *)
(*TIME      start_timer "sep_canceler:unfold_notation" ; *)
      let L := eval unfold empB, injB, injBX, starB, exB, hvarB in L in
      let R := eval unfold empB, injB, injBX, starB, exB, hvarB in R in
(*TIME      stop_timer "sep_canceler:unfold_notation" ; *)
(*TIME      start_timer "sep_canceler:reify" ; *)
      (** collect types **)
      let Ts := constr:(Reflect.Tnil) in
       ReifyExpr.collectTypes_exprs ltac:(isConst) pures Ts ltac:(fun Ts => 
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) L Ts ltac:(fun Ts =>
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) R Ts ltac:(fun Ts =>
      (** check for potential universe inconsistencies **)
      match Ts with
        | context [ PropX.PropX ] => 
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)" Ts
        | context [ PropX.spec ] => 
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)" Ts
        | _ => idtac 
      end ;
      (** elaborate the types **)
      let types_ := 
        reduce_repr (ILAlgoTypes.PACK.applyTypes (ILAlgoTypes.Env ext) nil)
      in
      let types_ := ReifyExpr.extend_all_types Ts types_ in
      let typesV := fresh "types" in
      pose (typesV := types_);
      (** build the variables **)
      let uvars := eval simpl in (@nil _ : Expr.env typesV) in
      let gvars := uvars in
      let vars := eval simpl in (@nil Expr.tvar) in
      (** build the funcs **)
      let funcs := reduce_repr (ILAlgoTypes.PACK.applyFuncs (ILAlgoTypes.Env ext) typesV nil) in
      let pcT := constr:(Expr.tvType 0) in
      let stT := constr:(Expr.tvType 1) in
      (** build the base sfunctions **)
      let preds := reduce_repr (ILAlgoTypes.PACK.applyPreds (ILAlgoTypes.Env ext) typesV nil) in
      ReifyExpr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
      let proofs := ReifyExpr.props_proof all_props in
      SEP_REIFY.reify_sexpr ltac:(isConst) L typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds L =>
      SEP_REIFY.reify_sexpr ltac:(isConst) R typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds R =>
(*TIME        stop_timer "sep_canceler:reify" ; *)
(*TIME        start_timer "sep_canceler:pose" ; *)
        let funcsV := fresh "funcs" in
        pose (funcsV := funcs) ;
        let predsV := fresh "preds" in
        pose (predsV := preds) ;
(*TIME          stop_timer "sep_canceler:pose" ; *)
(*TIME          start_timer "sep_canceler:apply_CancelSep" ; *)
        (((** TODO: for some reason the partial application to proofs doesn't always work... **)
         apply (@ApplyCancelSep typesV funcsV predsV 
                   (ILAlgoTypes.Algos ext typesV)
                   (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV) uvars pures L R); 
           [ apply proofs | reflexivity | ]
(*TIME       ;  stop_timer "sep_canceler:apply_CancelSep" *)
 )
        || (idtac "failed to apply, generalizing instead!" ;
            let algos := constr:(ILAlgoTypes.Algos ext typesV) in
            idtac "-" ;
            let algosC := constr:(@ILAlgoTypes.Algos_correct ext typesV funcsV predsV) in 
            idtac "*" ;
            first [ generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures L R) ; idtac "p"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures L)  ; idtac "o" 
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures) ; idtac "i"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars) ; idtac "u"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC) ; pose (uvars) ; idtac "y" 
                  | generalize (@ApplyCancelSep typesV funcsV predsV); pose (algosC) ; idtac "r" 
                  | generalize (@ApplyCancelSep typesV funcsV) ; idtac "q"
                  ])) ;
(*TIME          start_timer "sep_canceler:simplify" ; *)
           first [ simplifier typesV funcsV predsV tt | fail 100000 "canceler: simplifier failed" ] ;
(*TIME          stop_timer "sep_canceler:simplify" ; *)
(*TIME          start_timer "sep_canceler:clear" ; *)
           try clear typesV funcsV predsV
(*TIME        ;  stop_timer "sep_canceler:clear"  *)
        ))))))
    | [ |- ?G ] => 
      idtac "no match" G 
  end.

Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).
