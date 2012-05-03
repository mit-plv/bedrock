Require Import Bedrock.
Export Bedrock.

(** * Specialize the library proof automation to some parameters useful for basic examples. *)

Import SymILTac.
Require Bedrock.sep.PtsTo.

(** Build our memory plugin **)
Module Plugin_PtsTo := Bedrock.sep.PtsTo.BedrockPtsToEvaluator.

Definition TacPackage : Type := 
  @ILAlgoTypes.TypedPackage. (* ILEnv.bedrock_types_r (Expr.tvType 0) (Expr.tvType 1)
    SymIL.IL_mem_satisfies SymIL.IL_ReadWord SymIL.IL_WriteWord. *)

Definition auto_ext : TacPackage.
  ILAlgoTypes.Package.build_prover_pack Provers.ComboProver ltac:(fun a => 
  ILAlgoTypes.Package.build_mem_pack Plugin_PtsTo.ptsto32_pack ltac:(fun b =>
    ILAlgoTypes.Package.glue_packs (ILAlgoTypes.BedrockPackage.bedrock_package, a, b) ltac:(fun res => 
      let res := 
        eval cbv beta iota zeta delta [
          ILAlgoTypes.Env ILAlgoTypes.Algos ILAlgoTypes.Algos_correct
          PACK.Types PACK.Preds PACK.Funcs
          PACK.applyTypes PACK.applyFuncs PACK.applyPreds
          ILAlgoTypes.BedrockPackage.bedrock_package Env.repr_combine Env.footprint Env.nil_Repr
          Env.listToRepr
          app map
          
          ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r 
          ILAlgoTypes.AllAlgos_composite
          ILAlgoTypes.oplus Prover.composite_ProverT MEVAL.Composite.MemEvaluator_composite Env.listToRepr

          Plugin_PtsTo.ptsto32_ssig
        ] in res in
        ILAlgoTypes.Package.opaque_pack res) || fail 1000 "compose")).
Defined.

(*
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
*)

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

Ltac hints_ext_simplifier hints := fun H =>
  match H with
  | tt =>
      cbv beta iota zeta
       delta [hints 
         (** Symbolic Evaluation **)
         SymIL.MEVAL.Plugin.fold_first
         SymIL.MEVAL.Plugin.fold_first_update  SymIL.MEVAL.Plugin.plugin_symeval_read_word
         SymIL.MEVAL.Plugin.plugin_symeval_write_word
         SymIL.MEVAL.Plugin.MemEvaluator_plugin
         SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
         SymIL.MEVAL.LearnHookDefault.LearnHook_default 
         SymIL.IL_ReadWord SymIL.IL_WriteWord
         SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
         ILAlgoTypes.unfolder_LearnHook
         SymIL.MEVAL.Composite.MemEvaluator_composite
         SymIL.MEVAL.Default.smemeval_read_word_default
         SymIL.MEVAL.Default.smemeval_write_word_default
         SymIL.sym_evalInstrs
         SymIL.sym_evalInstr SymIL.sym_evalLval SymIL.sym_evalRval
         SymIL.sym_evalLoc SymIL.sym_evalStream SymIL.sym_assertTest
         SymIL.sym_setReg SymIL.sym_getReg
         SymIL.SymMem SymIL.SymRegs SymIL.SymPures
         SymIL.SymVars SymIL.SymUVars
         SymIL.stateD
         ILAlgoTypes.quantifyNewVars
         ILAlgoTypes.unfolder_LearnHook
         ILAlgoTypes.Hints ILAlgoTypes.Prover
         SymIL.MEVAL.smemeval_read_word SymIL.MEVAL.smemeval_write_word
         ILAlgoTypes.MemEval ILAlgoTypes.Env ILAlgoTypes.Algos
         ILAlgoTypes.unfolder_LearnHook
         (*SymIL.quantifyNewVars*) 
         ILAlgoTypes.Algos ILAlgoTypes.Hints ILAlgoTypes.Prover
   
         (** ILEnv **)
         ILEnv.comparator ILEnv.fPlus ILEnv.fMinus ILEnv.fMult
         ILEnv.bedrock_types_r ILEnv.bedrock_funcs_r 
         ILEnv.bedrock_types 
         ILEnv.BedrockCoreEnv.core
         ILEnv.BedrockCoreEnv.pc ILEnv.BedrockCoreEnv.st
             
         (** Env **)
         Env.repr_combine Env.default Env.footprint Env.repr'
         Env.updateAt Env.nil_Repr Env.repr Env.updateAt
         Env.repr_combine Env.footprint Env.default Env.repr

         (** Expr **)
         Expr.Range Expr.Domain Expr.Denotation Expr.Impl
         Expr.exists_subst Expr.forallEach Expr.existsEach
         Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
         Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
         Expr.tvar_rec Expr.tvar_rect Expr.liftExpr Expr.lookupAs Expr.Eq
         Expr.Provable Expr.tvar_val_sdec
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs Expr.AllProvable Expr.AllProvable_gen
         Expr.Provable Expr.tvarD
         Expr.expr_seq_dec
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs 
         Expr.tvarD Expr.Eq
         Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
         Expr.Default_signature Expr.EmptySet_type Expr.Impl Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect ExprUnify.get_Eq
         Expr.expr_seq_dec Expr.SemiDec_expr Expr.expr_seq_dec
         Expr.tvar_val_sdec Expr.Eq Expr.liftExpr Expr.exprSubstU
         Expr.typeof
         Expr.Impl_ Expr.exprD
         Expr.expr_ind

         (** ExprUnify **)
         ExprUnify.Subst_lookup ExprUnify.Subst_replace
         ExprUnify.env_of_Subst ExprUnify.get_Eq ExprUnify.exprUnifyArgs
         ExprUnify.exprUnify ExprUnify.empty_Subst ExprUnify.SUBST.empty
         ExprUnify.SUBST.find ExprUnify.SUBST.add
         ExprUnify.SUBST.remove
         ExprUnify.SUBST.fold ExprUnify.SUBST.map
         ExprUnify.fold_left_2_opt ExprUnify.Subst_lookup
         ExprUnify.Subst_replace ExprUnify.get_Eq ExprUnify.exprUnifyArgs
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.exprUnify ExprUnify.fold_left_2_opt
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.fold_left_3_opt
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.exprUnify ExprUnify.env_of_Subst
         Peano_dec.eq_nat_dec
         ExprUnify.fold_left_2_opt
         Expr.SemiDec_expr Expr.expr_seq_dec

         (** ExprUnify2 **)
         ExprUnify2.exprUnify ExprUnify2.exprInstantiate
         ExprUnify2.Subst_lookup ExprUnify2.Subst_equations
         ExprUnify2.empty_Subst ExprUnify2.anyb ExprUnify2.mentionsU
         ExprUnify2.get_Eq ExprUnify2.dep_in ExprUnify2.fold2_option
         ExprUnify2.SUBST.find ExprUnify2.Subst_replace 

         (** Unfolder **)
         Unfolder.FM.empty Unfolder.FM.add Unfolder.FM.remove
         Unfolder.FM.fold Unfolder.FM.map
         Unfolder.FM.find 
         UNF.Foralls UNF.Vars
         UNF.UVars UNF.Heap UNF.Hyps UNF.Lhs UNF.Rhs
         UNF.Forward UNF.forward UNF.unfoldForward UNF.Backward
         UNF.backward UNF.unfoldBackward UNF.findWithRest find equiv_dec 
         UNF.substExpr UNF.substSexpr
         UNF.fmFind UNF.findWithRest' 
         UNF.substSexpr Unfolder.allb UNF.substExpr
         UNF.find UNF.default_hintsPayload

         (** NatMap **)
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

         (** Prover **)
         Prover.Prove Prover.Summarize Prover.Learn
         Prover.Summarize Prover.Learn Prover.Prove
         Prover.composite_ProverT

         (** Provers **)
         Provers.transitivitySummarize Provers.transitivityLearn
         Provers.transitivityProve Provers.groupsOf Provers.addEquality
         Provers.proveEqual
         Provers.transitivityLearn Provers.inSameGroup 
         Provers.eqD_seq Provers.in_seq Provers.groupWith
         Provers.assumptionProver Provers.assumptionSummarize
         Provers.assumptionLearn Provers.assumptionProve
         Provers.transitivityProver
         Prover.Prove Prover.Facts
         Prover.Learn Prover.Summarize

         (** Induction **)
         list_ind list_rec list_rect 
         sumbool_rect sumbool_rec
         sumor_rec sumor_rect 
         nat_rec nat_rect nat_ind
         eq_rect_r eq_rec_r eq_rec eq_rect
         eq_sym f_equal 
         nat_rect eq_ind eq_rec eq_rect
         eq_sym
         eq_sym f_equal eq_rec_r eq_rect eq_rec nat_rec nat_rect
         sumbool_rec sumbool_rect
         sumbool_rec sumbool_rect
         sumor_rec sumor_rect
         nat_rec nat_rect

         (** Ordering **)
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_eq_lt_dec
         Peano_dec.eq_nat_dec
         EquivDec_nat Peano_dec.eq_nat_dec equiv_dec seq_dec
         Peano_dec.eq_nat_dec
         nat_eq_eqdec
         EquivDec_SemiDec
         Compare_dec.nat_compare

         (** SepExpr **)
         SEP.SDomain SEP.SDenotation SEP.liftSHeap SEP.sheapSubstU
         SEP.star_SHeap SepExpr.FM.empty SEP.multimap_join
         SEP.SHeap_empty SEP.sepCancel 
         SEP.unify_remove SEP.unifyArgs SEP.fold_left_3_opt SEP.sheapD
         SEP.starred SEP.himp SEP.sexprD SEP.hash SEP.sheap_liftVars
         SEP.SDenotation SEP.SDomain nat_eq_eqdec
         SEP.sheapD SEP.sepCancel SEP.star_SHeap 
         SEP.multimap_join SEP.liftSHeap SEP.unify_remove SEP.starred
         SEP.himp SEP.sexprD SEP.pures SEP.impures
         SEP.other SEP.star_SHeap SEP.liftSHeap
         SEP.multimap_join SEP.sheap_liftVars SEP.star_SHeap SEP.liftSHeap
         SEP.multimap_join SEP.hash SEP.Default_predicate
         SEP.impures SEP.pures SEP.other
         SepExpr.FM.map
         SepExpr.FM.find
         SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty
         SepExpr.FM.fold SepExpr.FM.find
         SepExpr.FM.add
         SEP.sheapD SEP.starred SEP.sexprD
         SepExpr.FM.fold SepExpr.FM.find
         SepExpr.FM.add SepExpr.FM.empty
         SEP.impures SEP.pures SEP.other
         (* SEP.unify_remove_all *)
         SEP.expr_count_meta SEP.meta_order_funcs SEP.meta_order_args
         SEP.order_impures 
         SEP.cancel_in_order
         Ordering.insert_in_order Ordering.list_lex_cmp Ordering.sort
         SEP.multimap_add

         (** PtsTo Plugin **)
         Plugin_PtsTo.ptsto32_ssig 
         Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
         Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
         Plugin_PtsTo.types 
         Plugin_PtsTo.MemEval_ptsto32

         (** General Recursion **)
         Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
         GenRec.guard Acc_rect well_founded_ind 
         well_founded_induction_type Acc_inv ExprUnify2.wf_R_expr  

         (** List Functions **)
         tl hd_error value error hd
         nth_error Datatypes.length fold_right firstn skipn rev
         rev_append map app fold_left

         (** Aux Functions **)
         fst snd projT1 projT2 Basics.impl value error 
         projT1 projT2 andb orb
         plus minus
         existsSubst

         (** ?? **)
         DepList.hlist_hd DepList.hlist_tl
         eq_sym

(*
             find 
             
              Plugin_PtsTo.MemEval_ptsto32
             SymIL.IL_mem_satisfies
              find Unfolder.FM.add
             
              fmFind
                substSexpr 
              SymIL.drop
                find 
             substSexpr Unfolder.FM.add  
            
              NatMap.IntMap.add
              

               
*)
             ]
  | _ =>
cbv beta iota zeta
       delta [hints 
         (** Symbolic Evaluation **)
         SymIL.MEVAL.Plugin.fold_first
         SymIL.MEVAL.Plugin.fold_first_update  SymIL.MEVAL.Plugin.plugin_symeval_read_word
         SymIL.MEVAL.Plugin.plugin_symeval_write_word
         SymIL.MEVAL.Plugin.MemEvaluator_plugin
         SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
         SymIL.MEVAL.LearnHookDefault.LearnHook_default 
         SymIL.IL_ReadWord SymIL.IL_WriteWord
         SymIL.MEVAL.Plugin.smem_read SymIL.MEVAL.Plugin.smem_write
         ILAlgoTypes.unfolder_LearnHook
         SymIL.MEVAL.Composite.MemEvaluator_composite
         SymIL.MEVAL.Default.smemeval_read_word_default
         SymIL.MEVAL.Default.smemeval_write_word_default
         SymIL.sym_evalInstrs
         SymIL.sym_evalInstr SymIL.sym_evalLval SymIL.sym_evalRval
         SymIL.sym_evalLoc SymIL.sym_evalStream SymIL.sym_assertTest
         SymIL.sym_setReg SymIL.sym_getReg
         SymIL.SymMem SymIL.SymRegs SymIL.SymPures
         SymIL.SymVars SymIL.SymUVars
         SymIL.stateD
         ILAlgoTypes.quantifyNewVars
         ILAlgoTypes.unfolder_LearnHook
         ILAlgoTypes.Hints ILAlgoTypes.Prover
         SymIL.MEVAL.smemeval_read_word SymIL.MEVAL.smemeval_write_word
         ILAlgoTypes.MemEval ILAlgoTypes.Env ILAlgoTypes.Algos
         ILAlgoTypes.unfolder_LearnHook
         (*SymIL.quantifyNewVars*) 
         ILAlgoTypes.Algos ILAlgoTypes.Hints ILAlgoTypes.Prover
   
         (** ILEnv **)
         ILEnv.comparator ILEnv.fPlus ILEnv.fMinus ILEnv.fMult
         ILEnv.bedrock_types_r ILEnv.bedrock_funcs_r 
         ILEnv.bedrock_types 
         ILEnv.BedrockCoreEnv.core
         ILEnv.BedrockCoreEnv.pc ILEnv.BedrockCoreEnv.st
             
         (** Env **)
         Env.repr_combine Env.default Env.footprint Env.repr'
         Env.updateAt Env.nil_Repr Env.repr Env.updateAt
         Env.repr_combine Env.footprint Env.default Env.repr

         (** Expr **)
         Expr.Range Expr.Domain Expr.Denotation Expr.Impl
         Expr.exists_subst Expr.forallEach Expr.existsEach
         Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
         Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
         Expr.tvar_rec Expr.tvar_rect Expr.liftExpr Expr.lookupAs Expr.Eq
         Expr.Provable Expr.tvar_val_sdec
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs Expr.AllProvable Expr.AllProvable_gen
         Expr.Provable Expr.tvarD
         Expr.expr_seq_dec
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs 
         Expr.tvarD Expr.Eq
         Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
         Expr.Default_signature Expr.EmptySet_type Expr.Impl Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect ExprUnify.get_Eq
         Expr.expr_seq_dec Expr.SemiDec_expr Expr.expr_seq_dec
         Expr.tvar_val_sdec Expr.Eq Expr.liftExpr Expr.exprSubstU
         Expr.typeof
         Expr.Impl_ Expr.exprD
         Expr.expr_ind

         (** ExprUnify **)
         ExprUnify.Subst_lookup ExprUnify.Subst_replace
         ExprUnify.env_of_Subst ExprUnify.get_Eq ExprUnify.exprUnifyArgs
         ExprUnify.exprUnify ExprUnify.empty_Subst ExprUnify.SUBST.empty
         ExprUnify.SUBST.find ExprUnify.SUBST.add
         ExprUnify.SUBST.remove
         ExprUnify.SUBST.fold ExprUnify.SUBST.map
         ExprUnify.fold_left_2_opt ExprUnify.Subst_lookup
         ExprUnify.Subst_replace ExprUnify.get_Eq ExprUnify.exprUnifyArgs
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.exprUnify ExprUnify.fold_left_2_opt
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.fold_left_3_opt
         ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
         ExprUnify.exprUnify ExprUnify.env_of_Subst
         Peano_dec.eq_nat_dec
         ExprUnify.fold_left_2_opt
         Expr.SemiDec_expr Expr.expr_seq_dec

         (** ExprUnify2 **)
         ExprUnify2.exprUnify ExprUnify2.exprInstantiate
         ExprUnify2.Subst_lookup ExprUnify2.Subst_equations
         ExprUnify2.empty_Subst ExprUnify2.anyb ExprUnify2.mentionsU
         ExprUnify2.get_Eq ExprUnify2.dep_in ExprUnify2.fold2_option
         ExprUnify2.SUBST.find ExprUnify2.Subst_replace 

         (** Unfolder **)
         Unfolder.FM.empty Unfolder.FM.add Unfolder.FM.remove
         Unfolder.FM.fold Unfolder.FM.map
         Unfolder.FM.find
         UNF.Foralls UNF.Vars
         UNF.UVars UNF.Heap UNF.Hyps UNF.Lhs UNF.Rhs
         UNF.Forward UNF.forward UNF.unfoldForward UNF.Backward
         UNF.backward UNF.unfoldBackward UNF.findWithRest find equiv_dec 
         UNF.substExpr UNF.substSexpr
         UNF.fmFind UNF.findWithRest' 
         UNF.substSexpr Unfolder.allb UNF.substExpr
         UNF.find UNF.default_hintsPayload

         (** NatMap **)
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
(*
         NatMap.IntMap.empty NatMap.IntMap.find
         NatMap.IntMap.insert_at_right NatMap.IntMap.remove
         NatMap.IntMap.map NatMap.IntMap.fold
         NatMap.Ordered_nat.compare NatMap.Ordered_nat.eq_dec
*)

         (** Prover **)
         Prover.Prove Prover.Summarize Prover.Learn
         Prover.Summarize Prover.Learn Prover.Prove
         Prover.composite_ProverT

         (** Provers **)
         Provers.transitivitySummarize Provers.transitivityLearn
         Provers.transitivityProve Provers.groupsOf Provers.addEquality
         Provers.proveEqual
         Provers.transitivityLearn Provers.inSameGroup 
         Provers.eqD_seq Provers.in_seq Provers.groupWith
         Provers.assumptionProver Provers.assumptionSummarize
         Provers.assumptionLearn Provers.assumptionProve
         Provers.transitivityProver
         Prover.Prove Prover.Facts
         Prover.Learn Prover.Summarize

         (** Induction **)
         list_ind list_rec list_rect 
         sumbool_rect sumbool_rec
         sumor_rec sumor_rect 
         nat_rec nat_rect nat_ind
         eq_rect_r eq_rec_r eq_rec eq_rect
         eq_sym f_equal 
         nat_rect eq_ind eq_rec eq_rect
         eq_sym
         eq_sym f_equal eq_rec_r eq_rect eq_rec nat_rec nat_rect
         sumbool_rec sumbool_rect
         sumbool_rec sumbool_rect
         sumor_rec sumor_rect
         nat_rec nat_rect

         (** Ordering **)
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_eq_lt_dec
         Peano_dec.eq_nat_dec
         EquivDec_nat Peano_dec.eq_nat_dec equiv_dec seq_dec
         Peano_dec.eq_nat_dec
         nat_eq_eqdec
         EquivDec_SemiDec
         Compare_dec.nat_compare

         (** SepExpr **)
         SEP.SDomain SEP.SDenotation SEP.liftSHeap SEP.sheapSubstU
         SEP.star_SHeap SepExpr.FM.empty SEP.multimap_join
         SEP.SHeap_empty SEP.sepCancel 
         SEP.unify_remove SEP.unifyArgs SEP.fold_left_3_opt SEP.sheapD
         SEP.starred SEP.himp SEP.sexprD SEP.hash SEP.sheap_liftVars
         SEP.SDenotation SEP.SDomain nat_eq_eqdec
         SEP.sheapD SEP.sepCancel SEP.star_SHeap 
         SEP.multimap_join SEP.liftSHeap SEP.unify_remove SEP.starred
         SEP.himp SEP.sexprD SEP.pures SEP.impures
         SEP.other SEP.star_SHeap SEP.liftSHeap
         SEP.multimap_join SEP.sheap_liftVars SEP.star_SHeap SEP.liftSHeap
         SEP.multimap_join SEP.hash SEP.Default_predicate
         SEP.impures SEP.pures SEP.other
         SepExpr.FM.map
         SepExpr.FM.find
         SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty
         SepExpr.FM.fold SepExpr.FM.find
         SepExpr.FM.add
         SEP.sheapD SEP.starred SEP.sexprD
         SepExpr.FM.fold SepExpr.FM.find
         SepExpr.FM.add SepExpr.FM.empty
         SEP.impures SEP.pures SEP.other
         (* SEP.unify_remove_all *)
         SEP.expr_count_meta SEP.meta_order_funcs SEP.meta_order_args
         SEP.order_impures 
         SEP.cancel_in_order
         Ordering.insert_in_order Ordering.list_lex_cmp Ordering.sort
         SEP.multimap_add

         (** PtsTo Plugin **)
         Plugin_PtsTo.ptsto32_ssig 
         Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
         Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
         Plugin_PtsTo.types 
         Plugin_PtsTo.MemEval_ptsto32

         (** General Recursion **)
         Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
         GenRec.guard Acc_rect well_founded_ind 
         well_founded_induction_type Acc_inv ExprUnify2.wf_R_expr  

         (** List Functions **)
         tl hd_error value error hd
         nth_error Datatypes.length fold_right firstn skipn rev
         rev_append map app fold_left

         (** Aux Functions **)
         fst snd projT1 projT2 Basics.impl value error 
         projT1 projT2 andb orb
         plus minus
         existsSubst

         (** ?? **)
         DepList.hlist_hd DepList.hlist_tl
         eq_sym

(*
             find 
             
              Plugin_PtsTo.MemEval_ptsto32
             SymIL.IL_mem_satisfies
              find Unfolder.FM.add
             
              fmFind
                substSexpr 
              SymIL.drop
                find 
             substSexpr Unfolder.FM.add  
            
              NatMap.IntMap.add
              

               
*)
             ] in H
  end;
  fold plus; fold minus;
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
               || (progress change (fix rev_append (l l' : list A) : list A :=
                 match l with
                   | nil => l'
                   | a1 :: l0 => rev_append l0 (a1 :: l')
                 end) with (@rev_append A))
           end.

Ltac evaluate ext := 
  ILAlgoTypes.sym_eval ltac:(isConst) ext ltac:(hints_ext_simplifier ext).

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
    | [ |- himp _ _ _ ] => progress cancel ext
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
  SymILTac.PACKAGED.prepareHints the_unfold_tac W (settings * state)%type isConst.

Ltac sep_auto := sep auto_ext.

Ltac prepare1 fwd bwd :=
  let env := eval simpl ILAlgoTypes.EnvOf in (ILAlgoTypes.EnvOf auto_ext) in
    prepare env fwd bwd ltac:(fun x => 
      ILAlgoTypes.Package.build_hints_pack x ltac:(fun x =>
        ILAlgoTypes.Package.glue_pack x auto_ext ltac:(fun X => refine X))).

Ltac prepare2 old :=
  let v := eval cbv beta iota zeta delta [ 
    auto_ext old
    ILAlgoTypes.AllAlgos_composite ILAlgoTypes.oplus
    PACK.Types PACK.Funcs PACK.Preds 
    ILAlgoTypes.Hints ILAlgoTypes.Prover ILAlgoTypes.MemEval
    ILAlgoTypes.Env ILAlgoTypes.Algos
    
    Env.repr_combine 
    Env.listToRepr
    app map 
  ] in old in
  ILAlgoTypes.Package.opaque_pack v.
