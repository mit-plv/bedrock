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
(*  Variable denote : expr types -> forall t : tvar, option (tvarD types t). *)
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

(*
(existsSubst funcs meta_env var_env subst 0 
              (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
               map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
              P)
*)
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

(*
Lemma existsSubst_existsEach_equations : forall ts (funcs : functions ts) vals sub meta_base vars_env from ret,
  existsSubst funcs meta_base vars_env sub from vals ret ->
  existsEach (map (@projT1 _ _) vals) (fun meta_env =>
    Subst_equations_to funcs meta_base vars_env sub from meta_env /\ ret meta_env).
Proof.
  induction vals; intros; simpl in *; auto.
  { destruct a. destruct o.
    { consider (U.Subst_lookup from sub); intros.
      { consider (exprD funcs meta_base vars_env e x); intros; try contradiction.
        exists t0. eapply IHvals in H1. eapply existsEach_sem in H1. eapply existsEach_sem.
        destruct H1. exists x0. intuition. simpl. rewrite H0. reflexivity. }
      { eapply IHvals in H0. eapply existsEach_sem in H0. simpl in *. 
        destruct H0. intuition. exists t. eapply existsEach_sem. exists x0. intuition. } }
    { consider (U.Subst_lookup from sub); intros.
      { consider (exprD funcs meta_base vars_env e x); intros; try contradiction.
        eapply IHvals in H1. eapply existsEach_sem in H1. destruct H1; intuition.
        exists t. apply existsEach_sem. exists x0. intuition; simpl.
        rewrite H0. reflexivity. }
      { destruct H0. exists x0. simpl in *. apply IHvals in H0. apply existsEach_sem in H0.
        apply existsEach_sem. destruct H0. exists x1. intuition. } } }      
Qed.

Lemma existsEach_existsSubst_equations : forall ts (funcs : functions ts) vals sub meta_base vars_env from ret,
  existsEach (map (@projT1 _ _) vals) (fun meta_env =>
    Subst_equations_to funcs meta_base vars_env sub from meta_env /\ ret meta_env) ->
  existsSubst funcs meta_base vars_env sub from vals ret.
Proof.
Admitted.

Lemma existsSubst_app : forall ts (fs : functions ts) meta_base vars_base sub a b from ret,
  existsSubst fs meta_base vars_base sub from (a ++ b) ret ->
  existsSubst fs meta_base vars_base sub from a (fun a_env =>
    existsSubst fs meta_base vars_base sub (from + length a) b (fun b_env => ret (a_env ++ b_env))).
Proof.
  induction a; intros; simpl in *.
  { rewrite Plus.plus_0_r. apply H. }
  { destruct a. destruct o.
    { consider (U.Subst_lookup from sub); intros.
      consider (exprD fs meta_base vars_base e x); intros.
      eapply IHa in H1. eapply existsSubst_sem in H1.

Lemma existsSubst_existsEach_equations : forall ts (funcs : functions ts) (meta_ext : variables) sub meta_base vars_env from ret,
  let vals := 
    map (fun x => existT (fun t => option (tvarD ts t)) (projT1 x) (Some (projT2 x))) meta_base ++
    map (fun x => existT (fun t => option (tvarD ts t)) x None) meta_ext
  in
  existsSubst funcs meta_base vars_env sub from vals ret ->
  existsEach meta_ext (fun meta_env =>
    Subst_equations_to funcs (meta_base ++ meta_env) vars_env sub from meta_env /\ ret (meta_base ++ meta_env)).
Proof.
  induction meta_ext; simpl; intros. 
  { rewrite app_nil_r in *. intuition.
    admit. }
  { 
    induction meta_base; simpl in *; auto.
    repeat match goal with
             | H : match ?X with _ => _ end |- _ =>
               consider X; intros
           end.

    Lemma existsSubst_allSome : forall 
      existsSubst funcs meta_base vars_env sub from
        (map
           (fun x : sigT (tvarD ts) =>
            existT (fun t : tvar => option (tvarD ts t)) 
              (projT1 x) (Some (projT2 x))) meta_base) ret ->
        ret
    
*)

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
          (*SH.liftSHeap 0 (length vars') ( *) SH.sheapSubstU 0 (length qr) (length uvars') rhs (* ) *)
        in
        let post :=
          {| UNF.Vars  := vars' (* List.app ql (rev (skipn (length ql) (vars'))) *)
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

  

  Lemma ApplyCancelSep_with_eq' : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),
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
            (SH.pures lhs')) (*
        Expr.forallEach ((*rev*) new_vars) (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
            (Expr.existsEach new_uvars (fun nus : Expr.env types =>
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
                  (SH.pures rhs')) )) ))
            (SH.pures lhs')) *)
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
(*
    cutrewrite (typeof_env (rev G) = rev v) in H7.
    Focus 2. subst. rewrite <- map_rev. reflexivity. *)
    destruct (UNF.forwardLength _ _ _ _ _ H2).
    eapply UNF.forwardOk  with (cs := cs) in H2; simpl; eauto using typeof_env_WellTyped_env.
    Focus 2. unfold WellTyped_env. subst. rewrite <- map_rev. auto.
    rewrite H2; clear H2. simpl.
    rewrite UNF.ST_EXT.himp_existsEach_p; [ reflexivity | intros ].
    simpl in *. destruct H8.
    consider (UNF.backward h p 10 f
           {| UNF.Vars := Vars
            ; UNF.UVars := UVars ++ rev v0
            ; UNF.Heap := SH.sheapSubstU 0 (length v0) (length UVars) s0 |}); intros.
    destruct (UNF.backwardLength _ _ _ _ _ H6); simpl in *.
    consider (CANCEL.sepCancel preds p (length UVars0) f Heap Heap0); intros.
    destruct p0. intuition; subst.
    eapply forallEach_sem in H1. Focus 2. instantiate (1 := rev G ++ G0).
    rewrite typeof_env_app. f_equal. rewrite <- map_rev. reflexivity.
    rewrite ListFacts.rw_skipn_app in H2. apply H2. repeat rewrite rev_length. rewrite map_length. auto.
    eapply AllProvable_impl_AllProvable in H1.
    
    Transparent UNF.backward UNF.forward Env.repr.
  Admitted.

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
  Proof.
    intros. eapply ApplyCancelSep_with_eq; eauto.
  Qed.

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

Ltac sep_canceler_base isConst ext simplifier :=
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

Add ML Path "reification". 
Declare ML Module "extlib".
Declare ML Module "reif". 

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
  let types := reduce_repr (ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext) nil) in
  let funcs := reduce_repr (ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext) types (Env.repr (bedrock_funcs_r types) nil)) in
  let preds := reduce_repr (ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext) types nil) in
  let all_props := ReifyExpr.collect_props ltac:(SEP_REIFY.reflectable shouldReflect) in 
  let pures := all_props in 
  
  let L := eval unfold empB, injB, injBX, starB, exB, hvarB in L in
  let R := eval unfold empB, injB, injBX, starB, exB, hvarB in R in   
      let k :=
            (fun types funcs uvars preds L R pures proofs => 
               (*TIME         stop_timer "sep_canceler:reify" *)

               ((** TODO: for some reason the partial application to proofs doesn't always work... **)
                 apply (@ApplyCancelSep types funcs preds
                         (ILAlgoTypes.Algos ext types)
                         (@ILAlgoTypes.Algos_correct ext types funcs preds) uvars pures L R); 
                [ apply proofs | reflexivity| ]                 
               (*TIME       ;  stop_timer "sep_canceler:apply_CancelSep" *)
               )
                 || (idtac "failed to apply, generalizing instead!" ;
                    let algos := constr:(ILAlgoTypes.Algos ext types) in
                    let algosC := constr:(@ILAlgoTypes.Algos_correct ext types funcs preds) in 
                    generalize (@ApplyCancelSep types funcs preds algos algosC uvars pures L R));
                 
             (*TIME          start_timer "sep_canceler:simplify" ; *)
           first [ simplifier types funcs preds tt | fail 100000 "canceler: simplifier failed" ] ;
             (*TIME          stop_timer "sep_canceler:simplify" ; *)
             (*TIME          start_timer "sep_canceler:clear" ; *)
           try clear types funcs preds
             (*TIME        ;  stop_timer "sep_canceler:clear"  *)
             )
      in
        (*TIME         start_timer "sep_canceler:reify"; *)

        (((sep_canceler_plugin types funcs preds pures L R k))
          (* || fail 10000 "sep_canceler_plugin failed" *))
    | [ |- ?G ] => 
        idtac "no match" G 
  end.

Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).
