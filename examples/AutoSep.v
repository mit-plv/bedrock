Require Import Bedrock.
Export Bedrock.

(** * Specialize the library proof automation to some parameters useful for basic examples. *)

Import SymIL.
Require Bedrock.sep.PtsTo.
Export UNF.

(** Build our memory plugin **)
Module Plugin_PtsTo := Bedrock.sep.PtsTo.BedrockPtsToEvaluator.

Definition TacPackage : Type := 
  @TypedPackage ILEnv.bedrock_types_r (Expr.tvType 0) (Expr.tvType 1)
    SymIL.IL_mem_satisfies SymIL.IL_ReadWord SymIL.IL_WriteWord.

Definition auto_ext' : TacPackage.  
  SymIL.Package.build_prover_pack Provers.ComboProver ltac:(fun a =>
  SymIL.Package.build_mem_pack Plugin_PtsTo.ptsto32_pack ltac:(fun b => 
    SymIL.Package.glue_packs (BedrockPackage.bedrock_package, a, b) ltac:(fun res => refine res) || fail 1000 "compose")).
Defined.

Definition auto_ext : TacPackage.
  let v := eval cbv beta iota zeta delta [ 
    auto_ext' BedrockPackage.bedrock_package
    Plugin_PtsTo.ptsto32_ssig MEVAL.Composite.MemEvaluator_composite 
    MEVAL.Default.MemEvaluator_default Prover.composite_ProverT Env.nil_Repr
    SymIL.AllAlgos_composite
    SymIL.oplus
    SymIL.Types SymIL.Funcs SymIL.Preds SymIL.Algos SymIL.Algos_correct

    ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r

    Env.repr_combine
    Env.listToRepr
    app map
    Provers.transitivityProver Provers.assumptionProver
    Prover.Summarize Prover.Facts Prover.Prove Prover.Learn
  ] in auto_ext' in
  SymIL.Package.opaque_pack v.
Defined.

Ltac vcgen :=
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.

Hint Extern 1 => tauto : contradiction.
Hint Extern 1 => congruence : contradiction.

Ltac sep_easy := auto with contradiction.

Lemma frame_reflexivity : forall pcT stateT p q specs,
  q = (fun pr => p (fst pr) (snd pr))
  -> himp (pcType := pcT) (stateType := stateT) specs p (fun st m => q (st, m)).
  intros; hnf; simpl; intros; subst.
  apply Imply_I; eauto.
Qed.

Ltac sep_firstorder := sep_easy;
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- Logic.ex _ ] => sep_easy; eexists
           | [ |- _ /\ _ ] => split
           | [ |- forall x, _ ] => intro
           | [ |- _ = _ ] => reflexivity
           | [ |- himp _ _ _ ] => reflexivity || (apply frame_reflexivity; reflexivity)
         end; sep_easy.

Ltac hints_ext_simplifier hints :=
fun H =>
  match H with
  | tt =>
      cbv beta iota zeta
       delta [hints Provers.assumptionProver Provers.assumptionSummarize
             Provers.assumptionLearn Provers.assumptionProve
             Expr.expr_seq_dec Provers.transitivityProver
             Provers.transitivitySummarize Provers.transitivityLearn
             Provers.transitivityProve Provers.groupsOf Provers.addEquality
             Provers.transitivityLearn Provers.inSameGroup Expr.expr_seq_dec
             Provers.eqD_seq Provers.in_seq Provers.groupWith
             SymIL.MEVAL.Plugin.fold_first
             SymIL.MEVAL.Plugin.fold_first_update SepExpr.FM.find
             SepExpr.FM.add SymIL.MEVAL.Plugin.plugin_symeval_read_word
             SymIL.MEVAL.Plugin.plugin_symeval_write_word
             SymIL.MEVAL.Plugin.MemEvaluator_plugin
             SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
             SymIL.MEVAL.LearnHookDefault.LearnHook_default Foralls Vars
             UVars Heap Hyps Lhs Rhs Forward forward unfoldForward Backward
             backward unfoldBackward findWithRest find equiv_dec substExpr
             substSexpr Unfolder.FM.add SEP.impures SEP.pures SEP.other
             Unfolder.allb andb Datatypes.length map app Expr.exprSubstU
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             SymIL.unfolder_LearnHook default_hintsPayload fmFind
             findWithRest' Plugin_PtsTo.MemEval_ptsto32
             Plugin_PtsTo.ptsto32_ssig SymIL.IL_mem_satisfies
             SymIL.IL_ReadWord SymIL.IL_WriteWord
             SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
             Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
             Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
             SymIL.MEVAL.Composite.MemEvaluator_composite
             SymIL.MEVAL.Default.smemeval_read_word_default
             SymIL.MEVAL.Default.smemeval_write_word_default
             Plugin_PtsTo.types Prover.composite_ProverT SymIL.sym_evalInstrs
             SymIL.sym_evalInstr SymIL.sym_evalLval SymIL.sym_evalRval
             SymIL.sym_evalLoc SymIL.sym_evalStream SymIL.sym_assertTest
             SymIL.sym_setReg SymIL.sym_getReg SEP.pures SEP.impures
             SEP.other SymIL.SymMem SymIL.SymRegs SymIL.SymPures
             SymIL.SymVars SymIL.SymUVars SEP.star_SHeap SEP.liftSHeap
             SEP.multimap_join Expr.SemiDec_expr Expr.expr_seq_dec
             Expr.tvar_val_sdec Expr.Eq Expr.liftExpr SEP.sheap_liftVars app
             map nth_error value error fold_right hd hd_error tl tl rev
             seq_dec DepList.hlist_hd DepList.hlist_tl SepExpr.FM.find
             SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty
             SepExpr.FM.fold Compare_dec.lt_eq_lt_dec nat_rec nat_rect
             Peano_dec.eq_nat_dec sumbool_rec sumbool_rect equiv_dec
             nat_eq_eqdec f_equal ILEnv.bedrock_funcs_r ILEnv.bedrock_types
             fst snd Env.repr Env.updateAt SymIL.stateD Expr.exprD
             Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
             Expr.lookupAs Expr.AllProvable Expr.AllProvable_gen
             Expr.Provable Expr.tvarD SEP.sheapD SEP.starred SEP.sexprD
             equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect eq_sym
             DepList.eq_sym f_equal eq_rec_r eq_rect eq_rec nat_rec nat_rect
             sumbool_rec sumbool_rect SEP.himp SEP.sexprD Expr.Impl
             Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
             Expr.lookupAs SEP.SDenotation SEP.SDomain nat_eq_eqdec
             SEP.sheapD SEP.sepCancel SEP.star_SHeap SEP.unify_remove_all
             SEP.multimap_join SEP.liftSHeap SEP.unify_remove SEP.starred
             Expr.tvarD Expr.Eq SepExpr.FM.fold SepExpr.FM.find
             SepExpr.FM.add SepExpr.FM.empty ILEnv.bedrock_types
             Compare_dec.lt_eq_lt_dec Peano_dec.eq_nat_dec SepExpr.FM.map
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             ExprUnify.exprUnify ExprUnify.fold_left_2_opt equiv_dec
             Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect ExprUnify.get_Eq
             orb Expr.typeof ILEnv.comparator ILEnv.fPlus ILEnv.fMinus
             ILEnv.fMult Env.repr_combine Env.default Env.footprint Env.repr'
             Env.updateAt Expr.Default_signature Env.nil_Repr
             Expr.EmptySet_type SEP.Default_predicate ILEnv.bedrock_funcs_r
             ILEnv.bedrock_types_r Prover.Summarize Prover.Learn Prover.Prove
             SymIL.MEVAL.smemeval_read_word SymIL.MEVAL.smemeval_write_word
             EquivDec_nat Peano_dec.eq_nat_dec Prover.Prove Prover.Facts
             Prover.Learn Prover.Summarize SymIL.Hints SymIL.Prover
             SymIL.MemEval SymIL.Funcs SymIL.Types SymIL.Preds SymIL.Algos
             Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
             Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
             ExprUnify.Subst_lookup ExprUnify.Subst_replace
             ExprUnify.env_of_Subst ExprUnify.get_Eq ExprUnify.exprUnifyArgs
             ExprUnify.exprUnify ExprUnify.empty_Subst ExprUnify.SUBST.empty
             ExprUnify.SUBST.find ExprUnify.SUBST.add
             ExprUnify.SUBST.insert_at_right ExprUnify.SUBST.remove
             ExprUnify.SUBST.remove_add ExprUnify.SUBST.find_add
             ExprUnify.SUBST.fold ExprUnify.SUBST.map
             NatMap.Ordered_nat.compare NatMap.Ordered_nat.eq_dec
             Peano_dec.eq_nat_dec ExprUnify.fold_left_2_opt
             ExprUnify.fold_left_3_opt sumor_rec sumor_rect Vars UVars Heap
             Foralls Hyps Lhs Rhs Forward Backward forward unfoldForward
             findWithRest find equiv_dec substExpr Unfolder.FM.add
             Unfolder.allb andb Datatypes.length map app Expr.exprSubstU
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             SymIL.unfolder_LearnHook default_hintsPayload fmFind
             findWithRest' findWithRest SEP.hash SEP.star_SHeap SEP.liftSHeap
             SEP.multimap_join map substExpr substSexpr rev_append
             Unfolder.FM.fold Unfolder.FM.add Unfolder.FM.empty
             Unfolder.FM.find Unfolder.FM.add Unfolder.FM.insert_at_right
             Unfolder.FM.remove Unfolder.FM.remove_add Unfolder.FM.find_add
             Unfolder.FM.fold Unfolder.FM.map plus minus SymIL.drop
             SymIL.quantifyNewVars Expr.Impl_ projT1 projT2 SymIL.Types
             SymIL.Preds SymIL.Funcs SymIL.Algos SymIL.Hints SymIL.Prover
             existsSubst Env.repr_combine Env.footprint Env.default Env.repr
             Expr.Range Expr.Domain Expr.Denotation Expr.Impl
             Expr.exists_subst Expr.forallEach Expr.existsEach
             Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
             Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
             Expr.tvar_rec Expr.tvar_rect Expr.liftExpr Expr.lookupAs Expr.Eq
             Expr.Provable Expr.tvar_val_sdec Prover.Prove Prover.Summarize
             Prover.Learn ExprUnify.exprUnify ExprUnify.env_of_Subst
             ExprUnify.fold_left_2_opt ExprUnify.Subst_lookup
             ExprUnify.Subst_replace ExprUnify.get_Eq ExprUnify.exprUnifyArgs
             ExprUnify2.exprUnify ExprUnify2.exprInstantiate
             ExprUnify2.Subst_lookup ExprUnify2.Subst_equations
             ExprUnify2.empty_Subst ExprUnify2.anyb ExprUnify2.mentionsU
             ExprUnify2.get_Eq ExprUnify2.dep_in ExprUnify2.fold2_option
             ExprUnify2.SUBST.find ExprUnify2.Subst_replace list_ind list_rec
             list_rect Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
             ExprUnify2.wf_R_expr well_founded_ind nat_ind
             well_founded_induction_type nat_rect eq_ind eq_rec eq_rect
             Acc_rect Expr.expr_ind Acc_inv SEP.impures SEP.pures SEP.other
             SEP.SDomain SEP.SDenotation SEP.liftSHeap SEP.sheapSubstU
             SEP.star_SHeap SepExpr.FM.empty SEP.multimap_join
             SEP.SHeap_empty SEP.sepCancel SEP.unify_remove_all
             SEP.unify_remove SEP.unifyArgs SEP.fold_left_3_opt SEP.sheapD
             SEP.starred SEP.himp SEP.sexprD SEP.hash SEP.sheap_liftVars Vars
             Foralls Hyps UVars Heap Lhs Rhs Forward forward unfoldForward
             Backward backward unfoldBackward findWithRest find substExpr
             substSexpr Unfolder.FM.add Unfolder.allb Expr.exprSubstU
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             SymIL.unfolder_LearnHook default_hintsPayload fmFind
             findWithRest' default_hintsPayload value error tl hd_error
             nth_error map Datatypes.length app fold_right firstn skipn
             Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
             Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec NatMap.IntMap.add
             NatMap.IntMap.empty NatMap.IntMap.find
             NatMap.IntMap.insert_at_right NatMap.IntMap.remove
             NatMap.IntMap.map NatMap.IntMap.fold EquivDec_nat sumbool_rec
             sumbool_rect sumor_rec sumor_rect nat_rec nat_rect eq_rect_r
             eq_rec_r eq_rec eq_rect eq_sym f_equal DepList.eq_sym
             Peano_dec.eq_nat_dec equiv_dec seq_dec EquivDec_SemiDec
             Expr.SemiDec_expr Expr.expr_seq_dec fst snd plus minus
             rev_append rev orb andb Unfolder.allb projT1 projT2 Basics.impl
             GenRec.guard]
  | _ =>
      cbv beta iota zeta
       delta [hints Provers.assumptionProver Provers.assumptionSummarize
             Provers.assumptionLearn Provers.assumptionProve
             Expr.expr_seq_dec Provers.transitivityProver
             Provers.transitivitySummarize Provers.transitivityLearn
             Provers.transitivityProve Provers.groupsOf Provers.addEquality
             Provers.transitivityLearn Provers.inSameGroup Expr.expr_seq_dec
             Provers.eqD_seq Provers.in_seq Provers.groupWith
             SymIL.MEVAL.Plugin.fold_first
             SymIL.MEVAL.Plugin.fold_first_update SepExpr.FM.find
             SepExpr.FM.add SymIL.MEVAL.Plugin.plugin_symeval_read_word
             SymIL.MEVAL.Plugin.plugin_symeval_write_word
             SymIL.MEVAL.Plugin.MemEvaluator_plugin
             SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
             SymIL.MEVAL.LearnHookDefault.LearnHook_default Foralls Vars
             UVars Heap Hyps Lhs Rhs Forward forward unfoldForward Backward
             backward unfoldBackward findWithRest find equiv_dec substExpr
             substSexpr Unfolder.FM.add SEP.impures SEP.pures SEP.other
             Unfolder.allb andb Datatypes.length map app Expr.exprSubstU
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             SymIL.unfolder_LearnHook default_hintsPayload fmFind
             findWithRest' Plugin_PtsTo.MemEval_ptsto32
             Plugin_PtsTo.ptsto32_ssig SymIL.IL_mem_satisfies
             SymIL.IL_ReadWord SymIL.IL_WriteWord
             SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
             Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
             Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
             SymIL.MEVAL.Composite.MemEvaluator_composite
             SymIL.MEVAL.Default.smemeval_read_word_default
             SymIL.MEVAL.Default.smemeval_write_word_default
             Plugin_PtsTo.types Prover.composite_ProverT SymIL.sym_evalInstrs
             SymIL.sym_evalInstr SymIL.sym_evalLval SymIL.sym_evalRval
             SymIL.sym_evalLoc SymIL.sym_evalStream SymIL.sym_assertTest
             SymIL.sym_setReg SymIL.sym_getReg SEP.pures SEP.impures
             SEP.other SymIL.SymMem SymIL.SymRegs SymIL.SymPures
             SymIL.SymVars SymIL.SymUVars SEP.star_SHeap SEP.liftSHeap
             SEP.multimap_join Expr.SemiDec_expr Expr.expr_seq_dec
             Expr.tvar_val_sdec Expr.Eq Expr.liftExpr SEP.sheap_liftVars app
             map nth_error value error fold_right hd hd_error tl tl rev
             seq_dec DepList.hlist_hd DepList.hlist_tl SepExpr.FM.find
             SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty
             SepExpr.FM.fold Compare_dec.lt_eq_lt_dec nat_rec nat_rect
             Peano_dec.eq_nat_dec sumbool_rec sumbool_rect equiv_dec
             nat_eq_eqdec f_equal ILEnv.bedrock_funcs_r ILEnv.bedrock_types
             fst snd Env.repr Env.updateAt SymIL.stateD Expr.exprD
             Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
             Expr.lookupAs Expr.AllProvable Expr.AllProvable_gen
             Expr.Provable Expr.tvarD SEP.sheapD SEP.starred SEP.sexprD
             equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect eq_sym
             DepList.eq_sym f_equal eq_rec_r eq_rect eq_rec nat_rec nat_rect
             sumbool_rec sumbool_rect SEP.himp SEP.sexprD Expr.Impl
             Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
             Expr.lookupAs SEP.SDenotation SEP.SDomain nat_eq_eqdec
             SEP.sheapD SEP.sepCancel SEP.star_SHeap SEP.unify_remove_all
             SEP.multimap_join SEP.liftSHeap SEP.unify_remove SEP.starred
             Expr.tvarD Expr.Eq SepExpr.FM.fold SepExpr.FM.find
             SepExpr.FM.add SepExpr.FM.empty ILEnv.bedrock_types
             Compare_dec.lt_eq_lt_dec Peano_dec.eq_nat_dec SepExpr.FM.map
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             ExprUnify.exprUnify ExprUnify.fold_left_2_opt equiv_dec
             Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect ExprUnify.get_Eq
             orb Expr.typeof ILEnv.comparator ILEnv.fPlus ILEnv.fMinus
             ILEnv.fMult Env.repr_combine Env.default Env.footprint Env.repr'
             Env.updateAt Expr.Default_signature Env.nil_Repr
             Expr.EmptySet_type SEP.Default_predicate ILEnv.bedrock_funcs_r
             ILEnv.bedrock_types_r Prover.Summarize Prover.Learn Prover.Prove
             SymIL.MEVAL.smemeval_read_word SymIL.MEVAL.smemeval_write_word
             EquivDec_nat Peano_dec.eq_nat_dec Prover.Prove Prover.Facts
             Prover.Learn Prover.Summarize SymIL.Hints SymIL.Prover
             SymIL.MemEval SymIL.Funcs SymIL.Types SymIL.Preds SymIL.Algos
             Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
             Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
             ExprUnify.Subst_lookup ExprUnify.Subst_replace
             ExprUnify.env_of_Subst ExprUnify.get_Eq ExprUnify.exprUnifyArgs
             ExprUnify.exprUnify ExprUnify.empty_Subst ExprUnify.SUBST.empty
             ExprUnify.SUBST.find ExprUnify.SUBST.add
             ExprUnify.SUBST.insert_at_right ExprUnify.SUBST.remove
             ExprUnify.SUBST.remove_add ExprUnify.SUBST.find_add
             ExprUnify.SUBST.fold ExprUnify.SUBST.map
             NatMap.Ordered_nat.compare NatMap.Ordered_nat.eq_dec
             Peano_dec.eq_nat_dec ExprUnify.fold_left_2_opt
             ExprUnify.fold_left_3_opt sumor_rec sumor_rect Vars UVars Heap
             Foralls Hyps Lhs Rhs Forward Backward forward unfoldForward
             findWithRest find equiv_dec substExpr Unfolder.FM.add
             Unfolder.allb andb Datatypes.length map app Expr.exprSubstU
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             SymIL.unfolder_LearnHook default_hintsPayload fmFind
             findWithRest' findWithRest SEP.hash SEP.star_SHeap SEP.liftSHeap
             SEP.multimap_join map substExpr substSexpr rev_append
             Unfolder.FM.fold Unfolder.FM.add Unfolder.FM.empty
             Unfolder.FM.find Unfolder.FM.add Unfolder.FM.insert_at_right
             Unfolder.FM.remove Unfolder.FM.remove_add Unfolder.FM.find_add
             Unfolder.FM.fold Unfolder.FM.map plus minus SymIL.drop
             SymIL.quantifyNewVars Expr.Impl_ projT1 projT2 SymIL.Types
             SymIL.Preds SymIL.Funcs SymIL.Algos SymIL.Hints SymIL.Prover
             existsSubst Env.repr_combine Env.footprint Env.default Env.repr
             Expr.Range Expr.Domain Expr.Denotation Expr.Impl
             Expr.exists_subst Expr.forallEach Expr.existsEach
             Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
             Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
             Expr.tvar_rec Expr.tvar_rect Expr.liftExpr Expr.lookupAs Expr.Eq
             Expr.Provable Expr.tvar_val_sdec Prover.Prove Prover.Summarize
             Prover.Learn ExprUnify.exprUnify ExprUnify.env_of_Subst
             ExprUnify.fold_left_2_opt ExprUnify.Subst_lookup
             ExprUnify.Subst_replace ExprUnify.get_Eq ExprUnify.exprUnifyArgs
             ExprUnify2.exprUnify ExprUnify2.exprInstantiate
             ExprUnify2.Subst_lookup ExprUnify2.Subst_equations
             ExprUnify2.empty_Subst ExprUnify2.anyb ExprUnify2.mentionsU
             ExprUnify2.get_Eq ExprUnify2.dep_in ExprUnify2.fold2_option
             ExprUnify2.SUBST.find ExprUnify2.Subst_replace list_ind list_rec
             list_rect Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
             ExprUnify2.wf_R_expr well_founded_ind nat_ind
             well_founded_induction_type nat_rect eq_ind eq_rec eq_rect
             Acc_rect Expr.expr_ind Acc_inv SEP.impures SEP.pures SEP.other
             SEP.SDomain SEP.SDenotation SEP.liftSHeap SEP.sheapSubstU
             SEP.star_SHeap SepExpr.FM.empty SEP.multimap_join
             SEP.SHeap_empty SEP.sepCancel SEP.unify_remove_all
             SEP.unify_remove SEP.unifyArgs SEP.fold_left_3_opt SEP.sheapD
             SEP.starred SEP.himp SEP.sexprD SEP.hash SEP.sheap_liftVars Vars
             Foralls Hyps UVars Heap Lhs Rhs Forward forward unfoldForward
             Backward backward unfoldBackward findWithRest find substExpr
             substSexpr Unfolder.FM.add Unfolder.allb Expr.exprSubstU
             ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
             SymIL.unfolder_LearnHook default_hintsPayload fmFind
             findWithRest' default_hintsPayload value error tl hd_error
             nth_error map Datatypes.length app fold_right firstn skipn
             Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
             Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec NatMap.IntMap.add
             NatMap.IntMap.empty NatMap.IntMap.find
             NatMap.IntMap.insert_at_right NatMap.IntMap.remove
             NatMap.IntMap.map NatMap.IntMap.fold EquivDec_nat sumbool_rec
             sumbool_rect sumor_rec sumor_rect nat_rec nat_rect eq_rect_r
             eq_rec_r eq_rec eq_rect eq_sym f_equal DepList.eq_sym
             Peano_dec.eq_nat_dec equiv_dec seq_dec EquivDec_SemiDec
             Expr.SemiDec_expr Expr.expr_seq_dec fst snd plus minus
             rev_append rev orb andb Unfolder.allb projT1 projT2 Basics.impl
             GenRec.guard] in H
  end.

Ltac evaluate ext := 
  sym_eval ltac:(isConst) ext ltac:(hints_ext_simplifier ext).

Ltac cancel ext :=
  sep_canceler ltac:(isConst) ext ltac:(hints_ext_simplifier ext); sep_firstorder.

Ltac unf := unfold substH.
Ltac reduce := Programming.reduce unf.
Ltac ho := Programming.ho unf; reduce.

Ltac step ext := 
  match goal with
    | [ |- _ _ = Some _ ] => solve [ eauto ]
    | [ |- interp _ (![ _ ] _) ] => cancel ext
    | [ |- interp _ (![ _ ] _ ---> ![ _ ] _)%PropX ] => cancel ext
    | _ => ho
  end.
Ltac descend := Programming.descend; reduce.

Ltac sep ext := 
  evaluate ext; descend; repeat (step ext; descend).

Ltac sepLemma := simpl; intros; cancel auto_ext.

(** env -> fwd -> bwd -> (hints -> T) -> T **)
Ltac prepare := 
  let the_unfold_tac x := 
    eval unfold empB injB injBX starB exB hvarB in x
  in
  SymIL.UNF.prepareHints the_unfold_tac W (settings * state)%type isConst.

Ltac sep_auto := sep auto_ext.

Ltac prepare1 fwd bwd :=
  let env := eval simpl SymIL.EnvOf in (SymIL.EnvOf auto_ext) in
    prepare env fwd bwd ltac:(fun x => 
      SymIL.Package.build_hints_pack x ltac:(fun x =>
        SymIL.Package.refine_glue_pack x auto_ext)).

Ltac prepare2 old :=
  let v := eval cbv beta iota zeta delta [ 
    auto_ext old
    SymIL.AllAlgos_composite SymIL.oplus
    SymIL.Types SymIL.Funcs SymIL.Preds SymIL.Hints SymIL.Prover SymIL.MemEval
    SymIL.Algos 
    
    Env.repr_combine 
    Env.listToRepr
    app map 
  ] in old in
  exact v.
