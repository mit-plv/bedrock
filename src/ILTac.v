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
  Check U.Subst_equations.
End existsSubst.

(*
Check existsSubst.

Lemma existsSubst_existsEach_equations : forall ts (funcs : functions ts) vals sub meta_base vars_env from ret,
  existsSubst funcs meta_base vars_env sub from vals ret ->
  existsEach (map (@projT1 _ _) vals) (fun meta_env =>
    U.Subst_equations funcs meta_env vars_env sub /\ ret meta_env).
Proof.
  induction vals; simpl; intros. 
  { intuition. SearchAbout U.Subst_equations.
*)
(*
Lemma apply_CancelSep : forall ts,
  let types := Env.repr BedrockCoreEnv.core ts in
  forall (funcs : functions types) (preds : SEP.predicates types BedrockCoreEnv.pc BedrockCoreEnv.st), 
  forall (algos : ILAlgoTypes.AllAlgos ts), ILAlgoTypes.AllAlgos_correct funcs preds algos ->
  forall prover hints,
    ProverT_correct prover funcs ->
    UNF.hintsSoundness funcs preds hints ->  
  forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_))
  (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st),
  Expr.AllProvable funcs meta_env nil hyps ->
  let (ql, lhs) := SH.hash l in
  let facts := Summarize prover (map (liftExpr 0 0 0 (length ql)) hyps ++ SH.pures lhs) in
  forall cs,
  let pre :=
    {| UNF.Vars  := ql
     ; UNF.UVars := map (@projT1 _ _) meta_env
     ; UNF.Heap  := lhs
     |}
  in
  match UNF.forward hints prover 10 facts pre with
    | {| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := lhs |} =>
      let (qr, rhs) := SH.hash r in
      let rhs := 
        (*SH.liftSHeap 0 (length vars') ( *) SH.sheapSubstU 0 (length qr) (length uvars') rhs (* ) *)
      in
      let post :=
        {| UNF.Vars  := List.app ql (rev (skipn (length ql) (vars')))
         ; UNF.UVars := uvars' ++ rev qr
         ; UNF.Heap  := rhs
         |}
      in
      match UNF.backward hints prover 10 facts post with
        | {| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := rhs |} =>
          let new_vars  := vars' in
          let new_uvars := skipn (length meta_env) uvars' in
          let bound := length uvars' in
          match CANCEL.sepCancel preds prover bound facts lhs rhs with
            | (lhs', rhs', subst) =>
              Expr.forallEach (rev new_vars) (fun nvs : Expr.env types =>
                let var_env := nvs in
                Expr.AllProvable_impl funcs meta_env var_env
                  (existsSubst (exprD funcs meta_env var_env) subst 0 
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
          end
      end
  end ->
  himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
          (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
Proof.
  Opaque UNF.backward UNF.forward Env.repr.


  Transparent UNF.backward UNF.forward Env.repr.
Admitted.
*)

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
    Lemma AllProvable_impl_AllProvable : forall U G P ps,
      AllProvable funcs U G ps ->
      AllProvable_impl funcs U G P ps ->
      P.
    Proof. clear. induction ps; simpl; intros; eauto. intuition. Qed.    
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
           [ apply proofs | vm_compute; reflexivity | ]
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
