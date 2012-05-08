Require Import IL SepIL SymILTac.
Require Import Word Memory.
Import List.
Require Import DepList EqdepClass.
Require Import PropX.
Require Import Expr SepExpr.
Require Import Prover ILEnv.

Set Implicit Arguments.
Set Strict Implicit.

(*
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.  
Add ML Path "/usr/local/lib/coq/user-contrib/". 
Declare ML Module "Timing_plugin".
*)

Section existsSubst.
  Variable types : list type.
  Variable denote : expr types -> forall t : tvar, option (tvarD types t).
  Variable sub : ExprUnify2.Subst types.
 
  Definition ExistsSubstNone (_ : list { t : tvar & option (tvarD types t) }) (_ : tvar) (_ : expr types) := False.
  Definition ExistsSubstSome (_ : list { t : tvar & option (tvarD types t) }) (_ : expr types) := False. 

  Fixpoint existsSubst (from : nat) (vals : list { t : tvar & option (tvarD types t) }) (ret : env types -> Prop) : Prop :=
    match vals with
      | nil => ret nil
      | existT t None :: vals =>
        match ExprUnify2.Subst_lookup from sub with
          | None => exists v : tvarD types t, existsSubst (S from) vals (fun env => ret (existT (tvarD types) t v :: env))
          | Some v =>
            match denote v t with
              | None => ExistsSubstNone vals t v
              | Some v => existsSubst (S from) vals (fun env => ret (existT (tvarD types) t v :: env))
            end
        end
      | existT t (Some v) :: vals =>
        match ExprUnify2.Subst_lookup from sub with
          | None => existsSubst (S from) vals (fun env => ret (existT (tvarD types) t v :: env))
          | Some v' =>
            match denote v' t with
              | None => ExistsSubstSome vals v'
              | Some v' => 
                existsSubst (S from) vals (fun env => v = v' /\ ret (existT (tvarD types) t v' :: env))
            end
        end
    end.
End existsSubst.

(** TODO : this isn't true **)
(** TODO : should we apply forward unfolding as well? **)
Lemma ApplyCancelSep : forall ts,
  let types := Env.repr BedrockCoreEnv.core ts in
  forall (funcs : functions types) (preds : SEP.predicates types BedrockCoreEnv.pc BedrockCoreEnv.st), 
  forall (algos : ILAlgoTypes.AllAlgos ts), ILAlgoTypes.AllAlgos_correct funcs preds algos ->
  let prover := 
    match ILAlgoTypes.Prover algos with
      | None => Provers.reflexivityProver
      | Some p => p
    end
  in
  let hints :=
    match ILAlgoTypes.Hints algos with
      | None => UNF.default_hintsPayload _ _ _ 
      | Some h => h
    end
  in
  forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_))
  (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st),
  Expr.AllProvable funcs meta_env nil hyps ->
  let (ql, lhs) := SEP.hash l in
  let (qr, rhs) := SEP.hash r in
  let facts := Summarize prover (map (liftExpr 0 (length ql)) hyps ++ SEP.pures lhs) in
  let rhs := SEP.liftSHeap 0 (length ql) (SEP.sheapSubstU 0 (length qr) (length meta_env) rhs) in
  forall cs,
  let initial := {| UNF.Vars := ql 
                  ; UNF.UVars := map (@projT1 _ _) meta_env ++ qr
                  ; UNF.Heap := rhs
                  |} in
  match UNF.backward hints prover 10 facts initial with
    | {| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := rhs |} =>
      (** NOTE: we're taking the first of them! **)
      let new_vars  := vars' in
      let new_uvars := skipn (length meta_env) uvars' in
      let bound := length uvars' in
      match SEP.sepCancel preds prover bound facts lhs rhs with
        | (lhs', rhs', subst) =>
          Expr.forallEach (rev new_vars) (fun nvs : Expr.env types =>
            let var_env := nvs in
            Expr.AllProvable_impl funcs meta_env var_env
            (** NOTE: I need to reverse this because 
             **) 
            (existsSubst (exprD funcs meta_env var_env) subst 0 
                (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
                 map (fun x => existT (fun t => option (tvarD types t)) x None) (rev new_uvars))
              (fun meta_env : Expr.env types =>
(*                Dyn (map (fun e => exprD funcs meta_env var_env e tvProp) (SEP.pures rhs') , meta_env, uvars, new_uvars) *)

                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures lhs') nil (SEP.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures rhs') nil (SEP.other rhs')))))
                  (SEP.pures rhs')) ))
                (SEP.pures lhs'))
(*          Dyn (SEP.pures rhs', 
               map (fun e => exprD funcs meta_env var_env e tvProp) (SEP.pures rhs'), 
               uvars, 
               uvars',
               meta_env)


*) 
(*
            exists_subst funcs VS uvars
              (ExprUnify.env_of_Subst subst uvars' 0)
 (** NOTE : we should combine lhs_subst and rhs_subst **)
              (fun uenv : Expr.env types =>
                let uvars := uenv ++ in
            Expr.AllProvable_impl funcs uvars (vars ++ VS)
                  (Expr.AllProvable_and funcs rhs_ex0 VS 
                    (himp cs 
                      (SEP.sexprD funcs preds rhs_ex0 VS
                        (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures lhs') nil (SEP.other lhs'))))
                      (SEP.sexprD funcs preds rhs_ex0 VS
                        (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures rhs') nil (SEP.other rhs'))))
                    ) (SEP.pures rhs')))) (SEP.pures lhs'))
*)
          
      end
  end ->
  himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
          (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
Proof.
  Opaque UNF.backward SEP.sepCancel.
  simpl.
  Transparent SEP.sepCancel UNF.backward.
Admitted.

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

Module SEP_REIFY := ReifySepExpr SEP.

(** The parameters are the following.
 ** - [isConst] is an ltac [* -> bool]
 ** - [ext] is a [TypedPackage .. .. .. .. ..]
 ** - [simplifier] is an ltac that simplifies the goal after the cancelation, it is passed
 **   constr:(tt).
 ** - [Ts] is a value of type [list Type] or [tt]
 **)
Ltac sep_canceler isConst ext simplifier :=
(*TIME  run_timer 10 ; *)
  (try change_to_himp) ;
(*TIME  stop_timer 10 ; *)
(*TIME  run_timer 11 ; *)
  let ext' := 
    match ext with
      | tt => eval cbv delta [ SymILTac.ILAlgoTypes.BedrockPackage.bedrock_package ] in SymILTac.ILAlgoTypes.BedrockPackage.bedrock_package
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
          PACK.applyTypes PACK.applyFuncs PACK.applyPreds PACK.Types PACK.Funcs PACK.Preds
          Env.repr Env.listToRepr Env.repr_combine Env.listOptToRepr Env.nil_Repr
          BedrockCoreEnv.core 
          ILAlgoTypes.Env
          tl map
          bedrock_types_r bedrock_funcs_r
        ] in ls
      | _ => 
        eval cbv beta iota zeta delta [
          PACK.applyTypes PACK.applyFuncs PACK.applyPreds PACK.Types PACK.Funcs PACK.Preds
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
(*TIME      stop_timer 11; *)
(*TIME      run_timer 12 ; *)
      let all_props := Expr.collect_props shouldReflect in
      let pures := Expr.props_types all_props in
(*TIME      stop_timer 12 ; *)
(*TIME      run_timer 13 ; *)
      let L := eval unfold empB injB injBX starB exB hvarB in L in
      let R := eval unfold empB injB injBX starB exB hvarB in R in
(*TIME      stop_timer 13 ; *)
(*TIME      run_timer 14 ; *)
      (** collect types **)
      let Ts := constr:(@nil Type) in
      let Ts := Expr.collectTypes_exprs ltac:(isConst) pures Ts in
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
        reduce_repr (PACK.applyTypes (ILAlgoTypes.Env ext) nil)
      in
      let types_ := Expr.extend_all_types Ts types_ in
      let typesV := fresh "types" in
      pose (typesV := types_);
      (** build the variables **)
      let uvars := eval simpl in (@nil _ : Expr.env typesV) in
      let gvars := uvars in
      let vars := eval simpl in (@nil Expr.tvar) in
      (** build the funcs **)
      let funcs := reduce_repr (PACK.applyFuncs (ILAlgoTypes.Env ext) typesV nil) in
      let pcT := constr:(Expr.tvType 0) in
      let stT := constr:(Expr.tvType 1) in
      (** build the base sfunctions **)
      let preds := reduce_repr (PACK.applyPreds (ILAlgoTypes.Env ext) typesV nil) in
      Expr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
      let proofs := Expr.props_proof all_props in
      SEP_REIFY.reify_sexpr ltac:(isConst) L typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds L =>
      SEP_REIFY.reify_sexpr ltac:(isConst) R typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds R =>
(*TIME        stop_timer 14 ; *)
(*TIME        run_timer 15 ; *)
        let funcsV := fresh "funcs" in
        pose (funcsV := funcs) ;
        let predsV := fresh "preds" in
        pose (predsV := preds) ;
(*TIME          stop_timer 15 ; *)
(*TIME          run_timer 16 ; *)
        ((** TODO: for some reason the partial application to proofs doesn't always work... **)
         apply (@ApplyCancelSep typesV funcsV predsV 
                   (SymILTac.ILAlgoTypes.Algos ext typesV)
                   (@SymILTac.ILAlgoTypes.Algos_correct ext typesV funcsV predsV) uvars pures L R); [ apply proofs | ];
(*         idtac "15" ; *)
(*TIME         stop_timer 16 ; *)
(*TIME         run_timer 17 ; *)
         (cbv delta [ ext typesV predsV funcsV ] || cbv delta [ typesV predsV funcsV ]) ;
         clear typesV predsV funcsV ;
(*TIME         stop_timer 17 ; *)
(*         idtac "16" ; *)
(*TIME         run_timer 18 ; *)
           simplifier tt
(*TIME         stop_timer 18  *)
 )
        || (idtac "failed to apply, generalizing instead!" ;
            let algos := constr:(SymILTac.ILAlgoTypes.Algos ext typesV) in
            idtac "-" ;
            let algosC := constr:(@SymILTac.ILAlgoTypes.Algos_correct ext typesV funcsV predsV) in 
            idtac "*" ;
            first [ generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures L R) ; idtac "p"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures L)  ; idtac "o" 
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures) ; idtac "i"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars) ; idtac "u"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC) ; pose (uvars) ; idtac "y" 
                  | generalize (@ApplyCancelSep typesV funcsV predsV); pose (algosC) ; idtac "r" 
                  | generalize (@ApplyCancelSep typesV funcsV) ; idtac "q"
                  ])
        )))))
    | [ |- ?G ] => 
      idtac "no match" G 
  end.

Ltac cancel_simplifier :=
  cbv beta iota zeta delta [
    (** Interface **)
    PACK.Types PACK.Preds PACK.Funcs
    PACK.applyTypes PACK.applyPreds PACK.applyFuncs
    ILAlgoTypes.Algos
    ILAlgoTypes.Hints ILAlgoTypes.Prover

    existsSubst
    
    (** TypeEnv **)
    BedrockCoreEnv.core BedrockCoreEnv.pc BedrockCoreEnv.st

    (** Env **)
    Env.repr_combine
    Env.footprint Env.default
    Env.repr

    (** Expr **)
    Expr.Range Expr.Domain Expr.Denotation Expr.Impl
    Expr.exists_subst
    Expr.forallEach Expr.existsEach
    Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
    Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_
    Expr.EqDec_tvar 
    Expr.tvar_rec Expr.tvar_rect
    Expr.liftExpr Expr.lookupAs
    Expr.Eq
    Expr.Provable Expr.tvar_val_sdec

    (** Prover **)
    Prover.Prove Prover.Summarize Prover.Learn

    (** ExprUnify **)
    ExprUnify.exprUnify
    ExprUnify.env_of_Subst ExprUnify.fold_left_2_opt
    ExprUnify.Subst_lookup ExprUnify.Subst_replace
    ExprUnify.get_Eq ExprUnify.exprUnifyArgs

    (** ExprUnify2 **)
    ExprUnify2.exprUnify
    ExprUnify2.exprInstantiate ExprUnify2.Subst_lookup 
    ExprUnify2.Subst_equations ExprUnify2.empty_Subst
    ExprUnify2.anyb ExprUnify2.mentionsU
    ExprUnify2.get_Eq
    ExprUnify2.dep_in ExprUnify2.fold2_option
    ExprUnify2.SUBST.find ExprUnify2.Subst_replace 
    list_ind list_rec list_rect
    (** * General recursion **)
    Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat ExprUnify2.wf_R_expr 
    well_founded_ind nat_ind 
    well_founded_induction_type nat_rect eq_ind eq_rec eq_rect
    Acc_rect Expr.expr_ind Acc_inv

    (** SepExpr **)
    SEP.impures SEP.pures SEP.other
    SEP.SDomain SEP.SDenotation

    SEP.liftSHeap SEP.sheapSubstU SEP.star_SHeap SepExpr.FM.empty SEP.multimap_join
    SEP.SHeap_empty

    SEP.sepCancel SEP.unify_remove SEP.unifyArgs SEP.fold_left_3_opt
    (*SEP.unify_remove_all*) 
    SEP.expr_count_meta SEP.meta_order_funcs SEP.meta_order_args
    SEP.order_impures Ordering.sort Ordering.insert_in_order
    SEP.cancel_in_order

    SEP.sheapD SEP.starred
    SEP.himp
    SEP.sexprD 

    SEP.hash SEP.sheap_liftVars

(*
    SepExpr.FM.find_add 
    SepExpr.FM.fold SepExpr.FM.find
      
    SepExpr.FM.add SepExpr.FM.insert_at_right SepExpr.FM.remove 
*)
    SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.fold SepExpr.FM.find SepExpr.FM.map

    (** Unfolder **)
    UNF.Vars UNF.Foralls UNF.Hyps UNF.UVars UNF.Heap UNF.Lhs UNF.Rhs
    UNF.Forward UNF.forward UNF.unfoldForward
    UNF.Backward UNF.backward UNF.unfoldBackward
    UNF.findWithRest UNF.find 
    UNF.substExpr UNF.substSexpr
    Unfolder.FM.add
    
    Unfolder.allb 
    exprSubstU
    
    ExprUnify.exprUnifyArgs ExprUnify.empty_Subst 

    ILAlgoTypes.unfolder_LearnHook
    UNF.default_hintsPayload
    UNF.fmFind
    UNF.findWithRest'

    UNF.default_hintsPayload
    Unfolder.FM.add Unfolder.FM.remove Unfolder.FM.fold Unfolder.FM.find Unfolder.FM.map

    (** List **)
    value error tl hd_error nth_error map length app fold_right firstn skipn

    (** IntMap **)
    Compare_dec.lt_dec
    Compare_dec.le_dec
    Compare_dec.le_gt_dec
    Compare_dec.le_lt_dec
    Compare_dec.lt_eq_lt_dec
(*
    NatMap.IntMap.add
    NatMap.IntMap.empty
    NatMap.IntMap.find
    NatMap.IntMap.insert_at_right
    NatMap.IntMap.remove
    NatMap.IntMap.map
    NatMap.IntMap.fold
*)
    NatMap.singleton
    NatMap.IntMap.height NatMap.IntMap.cardinal NatMap.IntMap.empty NatMap.IntMap.is_empty
    NatMap.IntMap.mem NatMap.IntMap.find NatMap.IntMap.assert_false NatMap.IntMap.create NatMap.IntMap.bal
    NatMap.IntMap.add NatMap.IntMap.remove_min NatMap.IntMap.merge NatMap.IntMap.remove NatMap.IntMap.join
    NatMap.IntMap.t_left NatMap.IntMap.t_opt NatMap.IntMap.t_right

    Int.Z_as_Int._0 Int.Z_as_Int._1 Int.Z_as_Int._2 Int.Z_as_Int._3
    Int.Z_as_Int.plus Int.Z_as_Int.max
    Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec

    ZArith_dec.Z_gt_le_dec ZArith_dec.Z_ge_lt_dec ZArith_dec.Z_ge_dec
    ZArith_dec.Z_gt_dec 
    ZArith_dec.Zcompare_rec ZArith_dec.Zcompare_rect

    BinInt.Z.add BinInt.Z.max BinInt.Z.pos_sub
    BinInt.Z.double BinInt.Z.succ_double BinInt.Z.pred_double
    
    BinInt.Z.compare

    BinPos.Pos.add BinPos.Pos.compare 
    BinPos.Pos.succ BinPos.Pos.compare_cont

    Compare_dec.nat_compare CompOpp 

    NatMap.Ordered_nat.compare

    sumor_rec sumor_rect
    sumbool_rec sumbool_rect
    eq_ind_r 

      
    (** EquivDec **)
    EquivDec_nat
    sumbool_rec sumbool_rect sumor_rec sumor_rect nat_rec nat_rect
    eq_rect_r eq_rec_r eq_rec eq_rect Logic.eq_sym Logic.f_equal eq_sym
    Peano_dec.eq_nat_dec equiv_dec
    seq_dec EquivDec_SemiDec SemiDec_expr 
    Expr.expr_seq_dec

    (** Other **)
    fst snd plus minus
    rev_append rev orb andb Unfolder.allb
    projT1 projT2
    Basics.impl

    (** wf_R_expr **)
    GenRec.guard
  ];
  (** TODO: Would it be better to make equivalent versions of these that the computational part of the
   ** tactics use?
   **)
  fold plus; fold minus; fold length; fold app;
  repeat match goal with
           | [ |- context[list ?A] ] =>
             progress change (fix length (l : list A) : nat :=
               match l with
                 | nil => 0
                 | _ :: l' => S (length l')
               end) with (@length A)
           | [ _ : list ?A |- _ ] =>
             progress change (fix app (l0 m : list A) : list A :=
               match l0 with
                 | nil => m
                 | a1 :: l1 => a1 :: app l1 m
               end) with (@app A)
             || (progress change (fix rev (l : list W) : list W :=
               match l with
                 | nil => nil
                 | x8 :: l' => (rev l' ++ x8 :: nil)%list
               end) with (@rev A))
         end.

Implicit Arguments existT [ A P ].

(*Theorem t3 : forall ls : list nat, [| (length ls > 0)%nat |] ===> Ex x, Ex ls', [| ls = x :: ls' |].
  destruct ls. Focus 2.
  sep_canceler ltac:(SymILTac.isConst) ILAlgoTypes.BedrockPackage.bedrock_package ltac:(fun _ => idtac).
  cbv delta [ ILAlgoTypes.BedrockPackage.bedrock_package ]; cancel_simplifier.
  intros. solve [ do 2 eexists; intuition ].
Abort.*)

Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).
