Require Import IL SepIL SymIL.
Require Import Word Memory.
Import List.
Require Import DepList EqdepClass.
Require Import PropX.
Require Import Expr SepExpr.
Require Import Prover ILEnv.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO : this isn't true **)
(** TODO : should we apply forward unfolding as well? **)
Lemma ApplyCancelSep : forall types funcs pcT stT preds A B C, 
  forall (algos : AllAlgos types pcT stT), AllAlgos_correct algos funcs preds A B C ->
  let prover := 
    match SymIL.Prover algos with
      | None => Provers.reflexivityProver
      | Some p => p
    end
  in
  let hints :=
    match SymIL.Hints algos with
      | None => UNF.default_hintsPayload _ _ _ 
      | Some h => h
    end
  in
  forall uvars (hyps : list (Expr.expr types))
  (l r : SEP.sexpr types pcT stT),
  Expr.AllProvable funcs uvars nil hyps ->
  let (ql, lhs) := SEP.hash l in
  let (qr, rhs) := SEP.hash r in
  let facts := Summarize prover (hyps ++ SEP.pures lhs) in
  let rhs := SEP.liftSHeap 0 (length ql) (SEP.sheapSubstU 0 (length qr) (length uvars) rhs) in
  forall cs,
  match UNF.backward hints prover 10 facts {| UNF.Vars := ql ; UNF.UVars := map (@projT1 _ _) uvars ++ qr ; UNF.Heap := rhs |} with
    | {| UNF.Vars := vars ; UNF.UVars := uvars' ; UNF.Heap := rhs |} =>
      let new_uvars := skipn (length uvars) uvars' in
      match SEP.sepCancel preds prover facts lhs rhs with
        | (lhs', rhs', lhs_subst, rhs_subst) =>
          Expr.forallEach vars (fun VS : Expr.env types =>
            Expr.AllProvable_impl funcs uvars VS
              (exists_subst funcs VS uvars
                (ExprUnify.env_of_Subst rhs_subst uvars' 0)
 (** NOTE : we should combine lhs_subst and rhs_subst **)
                (fun rhs_ex0 : Expr.env types =>
                  (Expr.AllProvable_and funcs rhs_ex0 VS 
                    (himp cs 
                      (SEP.sexprD funcs preds nil VS
                        (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures lhs') nil (SEP.other lhs'))))
                      (SEP.sexprD funcs preds rhs_ex0 VS
                        (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures rhs') nil (SEP.other rhs'))))
                    ) (SEP.pures rhs')))) (SEP.pures lhs'))
      end
  end ->
  himp cs (@SEP.sexprD _ _ _ funcs preds nil nil l)
          (@SEP.sexprD _ _ _ funcs preds uvars nil r).
Proof.
  simpl.
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
 ** - [simplifier] is an ltac that simplifies the goal after the cancelation
 ** - [Ts] is a value of type [list Type] or [tt]
 **)
Ltac sep_canceler isConst ext simplifier :=
  (try change_to_himp) ;
(*  idtac "-4" ; *)
  let ext' := 
    match ext with
      | tt => eval cbv delta [ BedrockPackage.bedrock_package ] in BedrockPackage.bedrock_package
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
    end
  in
(*  idtac "-3" ; *)
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
          Types Funcs Preds
          Env.repr Env.listToRepr Env.repr_combine Env.listOptToRepr Env.nil_Repr
          tl map
          bedrock_types_r bedrock_funcs_r
        ] in ls
      | _ => 
        eval cbv beta iota zeta delta [
          Types Funcs Preds
          Env.repr Env.listToRepr Env.repr_combine Env.listOptToRepr Env.nil_Repr
          tl map
          bedrock_types_r bedrock_funcs_r
        ] in ls
    end
  in
  let core_types :=
    match type of ext' with
      | TypedPackage ?ct _ _ _ _ _ => ct
      | ?T => fail 1000 "bad type " T 
    end
  in
  match goal with 
    | [ |- himp ?cs ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
(*      idtac "-2.5" ; *)
      let all_props := Expr.collect_props shouldReflect in
(*      idtac "-2" ; *)
      let pures := Expr.props_types all_props in
(*      idtac "-1: pures = " pures ; *)
      let L := eval unfold empB injB injBX starB exB hvarB in L in
      let R := eval unfold empB injB injBX starB exB hvarB in R in
      (** collect types **)
      let Ts := constr:(@nil Type) in
(*      idtac "0" ;  *)
      let Ts := Expr.collectTypes_exprs ltac:(isConst) pures Ts in
(*      idtac "1" ;  *)
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) L Ts ltac:(fun Ts =>
(*      idtac "2" ;  *)
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) R Ts ltac:(fun Ts =>
(*      idtac "3" ;  *)
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
(*      idtac "4" ;  *)
      (** elaborate the types **)
      let types_ := 
        reduce_repr (Env.repr core_types (Env.repr (Types ext) nil))
      in
(*      idtac "5" types_ ;  *)
      let types_ := Expr.extend_all_types Ts types_ in
(*      idtac "6" ;  *)
      let typesV := fresh "types" in
      pose (typesV := types_);
      (** build the variables **)
      let uvars := eval simpl in (@nil _ : Expr.env typesV) in
      let vars := eval simpl in (@nil Expr.tvar) in
(*      idtac "7" ;  *)
      (** build the funcs **)
      let funcs := reduce_repr (Env.repr (Funcs ext typesV) nil) in
      let pcT := constr:(Expr.tvType 0) in
      let stT := constr:(Expr.tvType 1) in
(*      idtac "8" ;  *)
      (** build the base sfunctions **)
      let preds := reduce_repr (Env.repr (Preds ext typesV) nil) in
(*      idtac "9" ;  *)
      Expr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
(*      idtac "10" ;  *)
        let proofs := Expr.props_proof all_props in
(*      idtac "11" ;  *)
      SEP_REIFY.reify_sexpr ltac:(isConst) L typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds L =>
      SEP_REIFY.reify_sexpr ltac:(isConst) R typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds R =>
(*        idtac "built terms" ;  *)
        let funcsV := fresh "funcs" in
        pose (funcsV := funcs) ;
        let predsV := fresh "preds" in
        pose (predsV := preds) ;
(*          idtac "12" ; *)
(*        idtac "14" ; *)
        ((** TODO: for some reason the partial application to proofs doesn't always work... **)
         apply (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ (SymIL.Algos ext typesV) (Algos_correct ext typesV funcsV predsV) uvars pures L R); [ apply proofs | ];
(*         idtac "15" ; *)
         (cbv delta [ ext typesV predsV funcsV ] || cbv delta [ typesV predsV funcsV ]) ;
(*         idtac "16" ; *)
         simplifier)
        || (idtac "failed to apply, generalizing instead!" ;
            let algos := constr:(SymIL.Algos ext typesV) in
            let algosC := constr:(Algos_correct ext typesV funcsV predsV) in 
            first [ generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ algos algosC uvars pures L R) ; idtac "p"
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ algos algosC uvars pures L)  ; idtac "o" 
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ algos algosC uvars pures) ; idtac "i"
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ algos algosC uvars) ; idtac "u"
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ algos algosC) ; pose (uvars) ; idtac "y" 
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV); pose (algosC) ; idtac "r" 
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT) ; idtac "e" 
                  | generalize (@ApplyCancelSep typesV funcsV pcT) ; idtac "w" 
                  | generalize (@ApplyCancelSep typesV funcsV) ; idtac "q"
                  ])
        )))))
    | [ |- ?G ] => 
      idtac "no match" G 
  end.

Ltac cancel_simplifier :=
  cbv beta iota zeta delta [
    (** Interface **)
    SymIL.Types SymIL.Preds SymIL.Funcs
    SymIL.Algos 
    SymIL.Hints SymIL.Prover

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

    (** SepExpr **)
    SEP.impures SEP.pures SEP.other
    SEP.SDomain SEP.SDenotation

    SEP.liftSHeap SEP.sheapSubstU SEP.star_SHeap SepExpr.FM.empty SEP.multimap_join
    SEP.substV SEP.SHeap_empty

    SEP.sepCancel SEP.unify_remove_all SEP.unify_remove SEP.unifyArgs
    ExprUnify.fold_left_3_opt

    SEP.sheapD SEP.starred
    SEP.himp
    SEP.sexprD 

    SEP.hash SEP.hash'

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

    unfolder_LearnHook
    UNF.default_hintsPayload
    UNF.fmFind
    UNF.findWithRest'

    UNF.default_hintsPayload

    (** List **)
    value error tl hd_error nth_error map length app fold_right firstn skipn

    (** IntMap **)
    Compare_dec.lt_dec
    Compare_dec.le_dec
    Compare_dec.le_gt_dec
    Compare_dec.le_lt_dec
    Compare_dec.lt_eq_lt_dec

    NatMap.IntMap.add
    NatMap.IntMap.empty
    NatMap.IntMap.find
    NatMap.IntMap.insert_at_right
    NatMap.IntMap.remove
    NatMap.IntMap.map
    NatMap.IntMap.fold

      
    (** EquivDec **)
    EquivDec_nat
    sumbool_rec sumbool_rect sumor_rec sumor_rect nat_rec nat_rect
    eq_rect_r eq_rec_r eq_rec eq_rect Logic.eq_sym Logic.f_equal DepList.eq_sym
    Peano_dec.eq_nat_dec equiv_dec
    seq_dec EquivDec_SemiDec SemiDec_expr 
    Expr.expr_seq_dec

    (** Other **)
    fst snd plus minus
    rev_append orb andb Unfolder.allb
    projT1 projT2
    Basics.impl
  ]; fold plus; fold minus; fold length; fold app;
  repeat match goal with
           | [ |- context[list ?A] ] =>
             progress change (fix length (l : list A) : nat :=
               match l with
                 | nil => 0
                 | _ :: l' => S (length l')
               end) with (@length A)
         end.


Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).
