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
(** TODO: I just need to fix the interface, so that it works out, i.e. use TypedPackage. **)
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
            Expr.existsEach new_uvars (fun US : Expr.env types =>
              exists_subst funcs VS (uvars ++ US) 
              (ExprUnify.env_of_Subst rhs_subst (map (@projT1 _ _) uvars ++ qr) 0)
 (** NOTE : we should combine lhs_subst and rhs_subst **)
              (fun rhs_ex0 : Expr.env types => 
                Expr.AllProvable_impl funcs uvars VS 
                (Expr.AllProvable_and funcs uvars VS 
                  (SEP.himp funcs preds nil rhs_ex0 VS cs
                    (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures lhs') nil (SEP.other lhs')))
                    (SEP.sheapD (SEP.Build_SHeap _ _ (SEP.impures rhs') nil (SEP.other rhs')))
                  ) (SEP.pures rhs')) (SEP.pures lhs'))))
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
  let ext := 
    match ext with
      | tt => EmptyAlgorithm.empty_package
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
    end
  in
  match goal with 
    | [ |- himp ?cs ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
      let all_props := Expr.collect_props ltac:(fun _ => true) in
      let pures := Expr.props_types all_props in
      let L := eval unfold starB exB hvarB in L in
      let R := eval unfold starB exB hvarB in R in
      (** collect types **)
      let Ts := constr:(@nil Type) in
(*      idtac "0" ; *)
      let Ts := Expr.collectTypes_exprs ltac:(isConst) pures Ts in
(*      idtac "1" ; *)
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) L Ts ltac:(fun Ts =>
(*      idtac "2" ; *)
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) R Ts ltac:(fun Ts =>
(*      idtac "3" ; *)
      (** check for potential universe inconsistencies **)
      match Ts with
        | context [ PropX.PropX ] => 
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)"
        | context [ PropX.spec ] => 
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)"
        | _ => idtac
      end ;
(*      idtac "4" ; *)
      (** elaborate the types **)
      match type of ext with
        | TypedPackage ?ct _ _ _ _ _ => idtac
        | ?T => fail 1000 "bad type " T 
      end ;
      let types_ :=       
        match type of ext with
          | TypedPackage ?ct _ _ _ _ _ =>
            Env.reduce_repr_list (Env.repr ct (Env.repr (Types ext) nil))
        end
      in
(*      idtac "5" ; *)
      let types_ := Expr.extend_all_types Ts types_ in
(*      idtac "6" ; *)
      let typesV := fresh "types" in
      pose (typesV := types_);
      (** build the variables **)
      let uvars := eval simpl in (@nil _ : Expr.env typesV) in
      let vars := eval simpl in (@nil _ : Expr.env typesV) in
(*      idtac "7" ; *)
      (** build the funcs **)
      let funcs := Env.reduce_repr_list (Env.repr (Funcs ext typesV) nil) in
      let pcT := constr:(Expr.tvType 0) in
      let stT := constr:(Expr.tvType 1) in
(*      idtac "8" ; *)
      (** build the base sfunctions **)
      let preds := Env.reduce_repr_list (Env.repr (Preds ext typesV) nil) in
(*      idtac "9" ; *)
      Expr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
(*      idtac "10" ; *)
        let proofs := Expr.props_proof all_props in
(*      idtac "11" ; *)
      SEP_REIFY.reify_sexpr ltac:(isConst) L typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds L =>
      SEP_REIFY.reify_sexpr ltac:(isConst) R typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds R =>
(*        idtac "built terms" ; *)
        let funcsV := fresh "funcs" in
        pose (funcsV := funcs) ;
        let predsV := fresh "preds" in
        pose (predsV := preds) ;
(*          idtac "12" ; *)
        let algosC := 
          eval cbv beta iota zeta delta [ Algos_correct Algos ] in
          (Algos_correct ext typesV funcsV predsV)
        in
(*        idtac "14" ; *)
        ((** TODO: for some reason the partial application to proofs doesn't always work... **)
         apply (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ _ algosC uvars pures L R); [ apply proofs | ];
(*         idtac "15" ; *)
         subst typesV ; subst predsV ; subst funcsV ;
(*         idtac "16" ; *)
         simplifier ;
(*         idtac "17" ; *)
         repeat match goal with
                  | [ H : _ /\ _ |- _ ] => destruct H
                  | [ |- exists x, _ ] => eexists
                  | [ |- _ /\ _ ] => (*idtac "splitting";*) split
                  | _ => reflexivity
                end)
        || (idtac "failed to apply, generalizing instead!" ; 
            first [ generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ _ algosC uvars pures L R) ; idtac "p"
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ _ algosC uvars pures L)  ; idtac "o" 
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ _ algosC uvars pures) ; idtac "i"
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ _ algosC uvars) ; idtac "u"
                  | generalize (@ApplyCancelSep typesV funcsV pcT stT predsV _ _ _ _ algosC) ; pose (uvars) ; idtac "y" 
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
    SEP.sepCancel
    SEP.hash SEP.hash' SEP.sepCancel

    SepExpr.FM.fold

    Facts Summarize Prove Learn

    ExprUnify.Subst
    
    ILEnv.bedrock_types ILEnv.bedrock_types_r
    ILEnv.bedrock_funcs ILEnv.bedrock_funcs_r
    app map fold_right nth_error value error hd hd_error tl
    
    fst snd

    SEP.star_SHeap SepExpr.FM.empty SEP.liftSHeap
    SEP.sheapSubstU ExprUnify.empty_Subst

    SEP.pures SEP.impures SEP.other

    exists_subst ExprUnify.env_of_Subst

    SEP.multimap_join SepExpr.FM.add SepExpr.FM.find SepExpr.FM.map

    SEP.unify_remove_all SEP.unify_remove

    SEP.unifyArgs
    ExprUnify.fold_left_2_opt ExprUnify.fold_left_3_opt
    Compare_dec.lt_eq_lt_dec nat_rec nat_rect 

    ExprUnify.exprUnify SEP.substV length
    Expr.liftExpr Expr.exprSubstU
    Peano_dec.eq_nat_dec EquivDec.equiv_dec 
    EquivDec_nat
    Expr.EqDec_tvar
    Expr.tvar_rec Expr.tvar_rect
    sumbool_rec sumbool_rect
    eq_rec_r eq_rect eq_rec f_equal eq_sym
    ExprUnify.get_Eq
    Expr.Eq
    EquivDec.nat_eq_eqdec
    Expr.typeof 
    Expr.expr_seq_dec
    Expr.tvarD
    Expr.tvar_val_sdec 
    Provers.groupWith
    Expr.Range Expr.Domain Expr.Denotation
    Expr.all2

    Expr.forallEach
    SEP.sheapD SEP.sexprD
    SEP.starred SEP.himp
    Expr.Impl Expr.Impl_ Expr.is_well_typed
    
    Env.repr_combine Env.default Env.footprint Env.repr' Env.updateAt 
    Expr.Default_signature Env.nil_Repr Expr.EmptySet_type SEP.Default_predicate

    orb

    SEP.liftSHeap SEP.hash SEP.hash'

    UNF.Forward UNF.Backward 
    UNF.backward

    SymIL.Hints SymIL.Prover
    Expr.existsEach Expr.forallEach
    firstn skipn
    AllProvable_gen

    (** Extra Stuff **)
    Compare_dec.lt_dec
    Compare_dec.le_dec
    Compare_dec.le_gt_dec
    Compare_dec.le_lt_dec
    Compare_dec.lt_eq_lt_dec

    ExprUnify.Subst_lookup ExprUnify.Subst_replace ExprUnify.env_of_Subst
    ExprUnify.get_Eq ExprUnify.exprUnifyArgs ExprUnify.exprUnify
    ExprUnify.empty_Subst

    ExprUnify.SUBST.empty
    ExprUnify.SUBST.find
    ExprUnify.SUBST.add
    ExprUnify.SUBST.insert_at_right
    ExprUnify.SUBST.remove
    ExprUnify.SUBST.remove_add
    ExprUnify.SUBST.find_add
    ExprUnify.SUBST.fold
    ExprUnify.SUBST.map

    NatMap.Ordered_nat.compare
    NatMap.Ordered_nat.eq_dec
    Peano_dec.eq_nat_dec
    
    ExprUnify.fold_left_2_opt ExprUnify.fold_left_3_opt
    sumor_rec sumor_rect
   
    UNF.Vars UNF.UVars UNF.Heap 
    UNF.Foralls UNF.Hyps UNF.Lhs UNF.Rhs 
    UNF.Forward UNF.Backward 
    UNF.backward UNF.unfoldBackward
    UNF.forward UNF.unfoldForward UNF.findWithRest UNF.find
    equiv_dec UNF.substExpr Unfolder.FM.add 
    Unfolder.allb length map app exprSubstU ExprUnify.exprUnifyArgs
    ExprUnify.empty_Subst unfolder_LearnHook
    UNF.default_hintsPayload UNF.fmFind UNF.findWithRest'
    UNF.findWithRest
        
    SEP.hash SEP.star_SHeap SEP.liftSHeap SEP.multimap_join map UNF.substExpr SEP.hash' UNF.substSexpr
    rev_append
    
    Unfolder.FM.fold Unfolder.FM.add
      
    Unfolder.FM.empty
    Unfolder.FM.find
    Unfolder.FM.add
    Unfolder.FM.insert_at_right
    Unfolder.FM.remove
    Unfolder.FM.remove_add
    Unfolder.FM.find_add
    Unfolder.FM.fold
    Unfolder.FM.map

    plus minus

    Expr.AllProvable_impl Expr.AllProvable_and
    Expr.AllProvable_impl Expr.AllProvable_and Expr.applyD 
    SEP.SDomain SEP.SDenotation
    Expr.exprD eq_sym eq_rec eq_rect

    eq_sym Logic.eq_sym
    projT1

  ].

Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).
