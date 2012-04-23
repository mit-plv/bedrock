Require Import AutoSep.

(** A very basic abstract predicate: pairs of words *)

Module Type PAIR.
  Parameter pair : W -> W -> W -> HProp.

  Axiom pair_extensional : forall a b p, HProp_extensional (pair a b p).

  Axiom pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.

  Axiom pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
End PAIR.

Module Pair : PAIR.
  Open Scope Sep_scope.

  Definition pair (a b p : W) : HProp :=
    p =*> a * (p ^+ $4) =*> b.

  Theorem pair_extensional : forall a b p, HProp_extensional (pair a b p).
    reflexivity.
  Qed.

  Theorem pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.
    sepLemma. 
  Qed.

  Theorem pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
    sepLemma.
  Qed.
End Pair.

Import Pair.
Hint Immediate pair_extensional.

Definition firstS : assert := st ~> ExX, Ex a, Ex b, ![ ^[pair a b st#Rv] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = a |] /\ ![ ^[pair a b st#Rv] * #1 ] st').

Definition pair := bmodule "pair" {{
  bfunction "first" [firstS] {
    Return $[Rv]
  }
}}.

Definition hints_pair' : TacPackage.
  prepare1 pair_fwd pair_bwd.
Defined.

Definition hints_pair : TacPackage.
  prepare2 hints_pair'.
Defined.

Ltac pair_ext_simplifier :=
fun H =>
  match H with
  | tt =>
      cbv beta iota zeta
       delta [hints_pair Provers.assumptionProver Provers.assumptionSummarize
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
       delta [hints_pair Provers.assumptionProver Provers.assumptionSummarize
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

Theorem pairOk : moduleOk pair.
  vcgen; abstract (sep hints_pair pair_ext_simplifier).
Qed.
