Require Import AutoSepExt.
Export AutoSepExt.

Ltac refold :=
  fold plus in *; fold minus in *;
    repeat match goal with
             | [ _ : list ?A |- _ ] =>
               progress change (fix length (l : list A) : nat :=
                 match l with
                   | nil => 0
                   | _ :: l' => S (length l')
                 end) with (@length A) in *
               || (progress change (fix app (l0 m : list A) : list A :=
                 match l0 with
                   | nil => m
                   | a1 :: l1 => a1 :: app l1 m
                 end) with (@app A) in *)
               || (progress change (fix rev (l : list W) : list W :=
                 match l with
                   | nil => nil
                   | x8 :: l' => (rev l' ++ x8 :: nil)%list
                 end) with (@rev A) in *)
               || (progress change (fix rev_append (l l' : list A) : list A :=
                 match l with
                   | nil => l'
                   | a1 :: l0 => rev_append l0 (a1 :: l')
                 end) with (@rev_append A) in *)
           end.

Require Import Bool.

Ltac vcgen_simp := cbv beta iota zeta delta [map app imps
  LabelMap.add Entry Blocks Postcondition VerifCond
  Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_ Use_
  Structured.If_ Structured.While_ Goto_ Structured.Call_ IGoto
  setArgs Programming.Reserved Programming.Formals Programming.Precondition
  importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
  List.fold_left ascii_lt string_lt label'_lt
  LabelKey.compare' LabelKey.compare LabelKey.eq_dec
  LabelMap.find
  toCmd Seq Instr Diverge Fail Skip Use_ Assert_
  Programming.If_ Programming.While_ Goto Programming.Call_ RvImm'
  Assign' variableSlot' localsInvariant
  regInL lvalIn immInR labelIn variableSlot string_eq ascii_eq
  andb eqb
].

Ltac vcgen :=
(*TIME time "vcgen:structured_auto" ( *)
  structured_auto vcgen_simp 
(*TIME ) *);
(*TIME time "vcgen:finish" ( *)
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold
(*TIME ) *).

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
           | [ H : Logic.ex _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- Logic.ex _ ] => sep_easy; eexists
           | [ |- _ /\ _ ] => split
           | [ |- forall x, _ ] => intro
           | [ |- _ = _ ] => reflexivity
           | [ |- himp _ _ _ ] => reflexivity || (apply frame_reflexivity; apply refl_equal)
         end; sep_easy; autorewrite with sepFormula;
  repeat match goal with
           | [ |- context[Regs (match ?st with
                                  | (_, y) => y
                                end) ?r] ] =>
             change (Regs (let (_, y) := st in y) r) with (st#r)
         end; try subst.

Require Import NArith.
Import TacPackIL.

Ltac hints_ext_simplifier hints := fun s1 s2 s3 H =>
  match H with
  | tt =>
      cbv beta iota zeta
       delta [s1 s2 s3 hints 
         (** Symbolic Evaluation **)
         SymIL.MEVAL.PredEval.fold_args
         SymIL.MEVAL.PredEval.fold_args_update SymIL.MEVAL.PredEval.pred_read_word
         SymIL.MEVAL.PredEval.pred_write_word
         SymIL.MEVAL.LearnHookDefault.LearnHook_default 
         SymIL.IL_ReadWord SymIL.IL_WriteWord
         SymILTac.unfolder_LearnHook
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
         SymILTac.Tactics.quantifyNewVars
         SymILTac.unfolder_LearnHook
         ILAlgoTypes.Hints ILAlgoTypes.Prover
         SymIL.MEVAL.sread_word SymIL.MEVAL.swrite_word
         ILAlgoTypes.MemEval ILAlgoTypes.Env ILAlgoTypes.Algos
         (*SymIL.quantifyNewVars*) 
         ILAlgoTypes.Algos ILAlgoTypes.Hints ILAlgoTypes.Prover
   
         (** ILEnv **)
         ILEnv.comparator ILEnv.fPlus ILEnv.fMinus ILEnv.fMult
         ILEnv.bedrock_types_r ILEnv.bedrock_funcs_r 
         ILEnv.bedrock_types 
         ILEnv.BedrockCoreEnv.core
         ILEnv.BedrockCoreEnv.pc ILEnv.BedrockCoreEnv.st
         ILEnv.bedrock_type_W ILEnv.bedrock_type_nat
         ILEnv.bedrock_type_setting_X_state
         ILEnv.bedrock_type_state
         ILEnv.bedrock_type_test
         ILEnv.bedrock_type_reg

         ILEnv.test_seq
         ILEnv.reg_seq
         ILEnv.W_seq

         ILEnv.word_nat_r
         ILEnv.word_state_r
         ILEnv.word_test_r
         
         ILEnv.wplus_r
         ILEnv.wminus_r
         ILEnv.wmult_r
         ILEnv.word_test_r
         ILEnv.wcomparator_r
         ILEnv.Regs_r
         ILEnv.wlt_r
         ILEnv.natToW_r

             
         (** Env **)
         Env.repr_combine Env.default Env.footprint Env.repr'
         Env.updateAt Env.nil_Repr Env.repr Env.updateAt
         Env.repr_combine Env.footprint Env.default Env.repr

         (** Expr **)
         Expr.Range Expr.Domain Expr.Denotation Expr.Impl Expr.Eqb
         Expr.exists_subst Expr.forallEach Expr.existsEach
         Expr.AllProvable Expr.AllProvable_gen
         Expr.AllProvable_and Expr.AllProvable_impl
         Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
         Expr.liftExpr Expr.lookupAs
         Expr.Provable Expr.tvar_val_seqb
         Expr.Provable Expr.tvarD
         Expr.tvar_rec Expr.tvar_rect
         Expr.Default_signature Expr.EmptySet_type
         Expr.expr_seq_dec 
         Expr.Eqb Expr.liftExpr Expr.exprSubstU
         Expr.typeof
         Expr.expr_ind
         Expr.get_Eq
         Expr.const_seqb
         Expr.tvar_seqb
         Expr.tvar_val_seqb_correct
         Expr.tvar_seqb_correct
         Expr.mentionsU
         ReifyExpr.default_type
         
         (** ExprUnify **)
         U.exprUnify U.exprUnify_recursor
         U.exprInstantiate U.subst_exprInstantiate
         U.Subst_lookup U.subst_lookup
         U.Subst_empty U.subst_empty
         U.Subst_set U.subst_set
         U.Subst_equations
         U.Subst_size
         U.dep_in
         U.exprUnify_recursor

         U.FM.Raw.height U.FM.Raw.cardinal U.FM.Raw.assert_false U.FM.Raw.create
         U.FM.Raw.bal U.FM.Raw.remove_min U.FM.Raw.merge U.FM.Raw.join
         U.FM.Raw.t_left U.FM.Raw.t_opt U.FM.Raw.t_right
         U.FM.Raw.cardinal U.FM.Raw.empty U.FM.Raw.is_empty
         U.FM.Raw.mem U.FM.Raw.find   
         U.FM.Raw.add  U.FM.Raw.remove
         U.FM.Raw.fold U.FM.Raw.map U.FM.Raw.mapi U.FM.Raw.map2

         U.FM.this U.FM.is_bst
         U.FM.empty U.FM.is_empty
         U.FM.add U.FM.remove
         U.FM.mem U.FM.find
         U.FM.map U.FM.mapi U.FM.map2
         U.FM.elements U.FM.cardinal U.FM.fold
         U.FM.equal
         U.FM.E.eq_dec

         (** Unfolder **)
         Unfolder.FM.empty Unfolder.FM.add Unfolder.FM.remove
         Unfolder.FM.fold Unfolder.FM.map
         Unfolder.FM.find 
         UNF.Vars UNF.UVars UNF.Heap
         UNF.LEM.Foralls UNF.LEM.Hyps UNF.LEM.Lhs UNF.LEM.Rhs
         UNF.Forward UNF.forward UNF.unfoldForward
         UNF.Backward UNF.backward UNF.unfoldBackward
         UNF.findWithRest UNF.find equiv_dec 
         UNF.findWithRest' 
         Folds.allb 
         UNF.find UNF.default_hintsPayload
         UNF.openForUnification 
         UNF.quant
         UNF.liftInstantiate
         UNF.applySHeap
         UNF.applicable UNF.checkAllInstantiated


         (** NatMap **)
         NatMap.singleton
         NatMap.IntMap.Raw.height NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.assert_false NatMap.IntMap.Raw.create
         NatMap.IntMap.Raw.bal NatMap.IntMap.Raw.remove_min NatMap.IntMap.Raw.merge NatMap.IntMap.Raw.join
         NatMap.IntMap.Raw.t_left NatMap.IntMap.Raw.t_opt NatMap.IntMap.Raw.t_right
         NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.empty NatMap.IntMap.Raw.is_empty
         NatMap.IntMap.Raw.mem NatMap.IntMap.Raw.find   
         NatMap.IntMap.Raw.add  NatMap.IntMap.Raw.remove
         NatMap.IntMap.Raw.fold NatMap.IntMap.Raw.map NatMap.IntMap.Raw.mapi NatMap.IntMap.Raw.map2

         NatMap.IntMap.this NatMap.IntMap.is_bst
         NatMap.IntMap.empty NatMap.IntMap.is_empty
         NatMap.IntMap.add NatMap.IntMap.remove
         NatMap.IntMap.mem NatMap.IntMap.find
         NatMap.IntMap.map NatMap.IntMap.mapi NatMap.IntMap.map2
         NatMap.IntMap.elements NatMap.IntMap.cardinal NatMap.IntMap.fold
         NatMap.IntMap.equal
        
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
         Prover.Prove Prover.Prover Prover.Facts Prover.Learn Prover.Summarize
         Prover.composite_ProverT

         (** Provers **)
         Provers.ComboProver

         (** TransitivityProver **)
         provers.TransitivityProver.transitivitySummarize 
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.transitivityProve
         provers.TransitivityProver.groupsOf 
         provers.TransitivityProver.addEquality
         provers.TransitivityProver.proveEqual
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.inSameGroup 
         provers.TransitivityProver.in_seq 
         provers.TransitivityProver.groupWith
         provers.TransitivityProver.transitivityProver

         (** AssumptionProver **)
         provers.AssumptionProver.assumptionProver 
         provers.AssumptionProver.assumptionSummarize
         provers.AssumptionProver.assumptionLearn
         provers.AssumptionProver.assumptionProve

         (** ReflexivityProver **)
         provers.ReflexivityProver.reflexivityProver 
         provers.ReflexivityProver.reflexivitySummarize
         provers.ReflexivityProver.reflexivityLearn
         provers.ReflexivityProver.reflexivityProve

         (** WordProver **)
         provers.WordProver.wordProver provers.WordProver.Source provers.WordProver.Destination provers.WordProver.Difference
         provers.WordProver.pow32 provers.WordProver.wplus' provers.WordProver.wneg' provers.WordProver.wminus' wordBin NToWord Nplus minus
         provers.WordProver.decompose combine Expr.expr_seq_dec provers.WordProver.combineAll provers.WordProver.combine app
         provers.WordProver.alreadyCovered provers.WordProver.alreadyCovered' andb orb provers.WordProver.merge provers.WordProver.wordLearn1 provers.WordProver.wordLearn
         provers.WordProver.equalitysEq ILEnv.W_seq weq provers.WordProver.equalityMatches provers.WordProver.wordProve provers.WordProver.wordSummarize
         provers.WordProver.types ILEnv.bedrock_type_W provers.WordProver.zero Bool.bool_dec wzero' posToWord bool_rec bool_rect
         Nminus wordToN Nsucc Nmult Pos.mul Pos.add Pos.sub_mask Pos.succ_double_mask Pos.double_mask Pos.pred_double
         provers.WordProver.natToWord' mod2 Div2.div2 whd wtl Pos.double_pred_mask
         provers.WordProver.Equalities provers.WordProver.LessThans provers.WordProver.NotEquals
         provers.WordProver.lessThanMatches

         (** Induction **)
         list_ind list_rec list_rect 
         sumbool_rect sumbool_rec
         nat_rect nat_ind
         eq_rect_r eq_rec_r eq_rec eq_rect eq_ind
         eq_sym f_equal
         sumbool_rec sumbool_rect
         sumbool_rec sumbool_rect
         sumor_rec sumor_rect
         nat_rec nat_rect

         (** Comparisons **)
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_eq_lt_dec
         Peano_dec.eq_nat_dec
         EquivDec_nat equiv_dec seq_dec
         nat_eq_eqdec
         EquivDec_SemiDec
         Compare_dec.nat_compare
         NPeano.leb NPeano.ltb

         (** SepExpr **)
         SEP.SDomain SEP.SDenotation 
         SEP.Default_predicate
         SEP.himp SEP.sexprD
         SEP.heq
         SEP.liftSExpr

         (** SepHeap **)
         SH.impures SH.pures SH.other
         SH.liftSHeap SH.sheapSubstU
         SH.starred SH.hash 
         SH.star_SHeap 
         SH.SHeap_empty 
         SH.sheapD

         SepHeap.FM.empty
         SepHeap.FM.map
         SepHeap.FM.find
         SepHeap.FM.add 
         SepHeap.FM.remove 
         SepHeap.FM.fold

         (** SepCancel **)
         CANCEL.sepCancel 
         CANCEL.expr_count_meta CANCEL.expr_size CANCEL.meta_order_funcs CANCEL.meta_order_args
         CANCEL.order_impures 
         CANCEL.cancel_in_order
         CANCEL.unify_remove CANCEL.unifyArgs
         
         (** Ordering **)
         Ordering.insert_in_order Ordering.list_lex_cmp Ordering.sort
         
         (** Multimaps **)
         SepHeap.MM.mmap_add SepHeap.MM.mmap_extend SepHeap.MM.mmap_join
         SepHeap.MM.mmap_mapi SepHeap.MM.mmap_map
         SepHeap.MM.empty

         (** PtsTo Plugin **)
         Plugin_PtsTo.ptsto32_ssig 
         Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
         Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
         Plugin_PtsTo.types 
         Plugin_PtsTo.MemEval_ptsto32
         Plugin_PtsTo.MemEvaluator_ptsto32

         (** General Recursion **)
         Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
         GenRec.guard Acc_rect well_founded_ind 
         well_founded_induction_type Acc_inv ExprUnify.wf_R_expr  

         (** Folds **)
         Folds.fold_left_2_opt Folds.fold_left_3_opt

         (** List Functions **)
         tl hd_error value error hd
         nth_error Datatypes.length fold_right firstn skipn rev
         rev_append map app fold_left

         (** Aux Functions **)
         fst snd projT1 projT2 Basics.impl value error 
         projT1 projT2 andb orb
         plus minus
         existsSubst

         (** Reflection **)
         (* Reflection.Reflect_eqb_nat *)

         (** Array *)
         Array.ssig Array.types_r Array.types
         Array.MemEval Array.MemEvaluator
         Array.div4 Array.deref Array.sym_read Array.sym_write
         Array.wlength_r Array.sel_r Array.upd_r

         (** Locals *)
         Locals.bedrock_type_string Locals.bedrock_type_listString Locals.bedrock_type_vals
         Locals.ssig Locals.types_r Locals.types
         Locals.MemEval Locals.MemEvaluator
         Locals.ascii_eq Locals.string_eq Bool.eqb
         Locals.nil_r Locals.cons_r Locals.sel_r Locals.upd_r
         Locals.deref Locals.listIn Locals.sym_sel Locals.sym_read Locals.sym_write

         (** ?? **)
         DepList.hlist_hd DepList.hlist_tl
         eq_sym eq_trans
         EqNat.beq_nat 


         (** TODO: sort these **)
          ILAlgoTypes.Env ILAlgoTypes.Algos ILAlgoTypes.Algos_correct
          ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Preds ILAlgoTypes.PACK.Funcs
          ILAlgoTypes.PACK.applyTypes
          ILAlgoTypes.PACK.applyFuncs
          ILAlgoTypes.PACK.applyPreds

          ILAlgoTypes.BedrockPackage.bedrock_package
          Env.repr_combine Env.footprint Env.nil_Repr
          Env.listToRepr
          app map
          
          ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r 
          ILAlgoTypes.AllAlgos_composite
          ILAlgoTypes.oplus Prover.composite_ProverT 
          (*TacPackIL.MEVAL.Composite.MemEvaluator_composite*) Env.listToRepr

          Plugin_PtsTo.ptsto32_ssig Bedrock.sep.Array.ssig
       ]
  | _ =>
    cbv beta iota zeta
       delta [s1 s2 s3 hints 
         (** Symbolic Evaluation **)
         SymIL.MEVAL.PredEval.fold_args
         SymIL.MEVAL.PredEval.fold_args_update SymIL.MEVAL.PredEval.pred_read_word
         SymIL.MEVAL.PredEval.pred_write_word
         SymIL.MEVAL.LearnHookDefault.LearnHook_default 
         SymIL.IL_ReadWord SymIL.IL_WriteWord
         SymILTac.unfolder_LearnHook
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
         SymILTac.Tactics.quantifyNewVars
         SymILTac.unfolder_LearnHook
         ILAlgoTypes.Hints ILAlgoTypes.Prover
         SymIL.MEVAL.sread_word SymIL.MEVAL.swrite_word
         ILAlgoTypes.MemEval ILAlgoTypes.Env ILAlgoTypes.Algos
         (*SymIL.quantifyNewVars*) 
         ILAlgoTypes.Algos ILAlgoTypes.Hints ILAlgoTypes.Prover
   
         (** ILEnv **)
         ILEnv.comparator ILEnv.fPlus ILEnv.fMinus ILEnv.fMult
         ILEnv.bedrock_types_r ILEnv.bedrock_funcs_r 
         ILEnv.bedrock_types 
         ILEnv.BedrockCoreEnv.core
         ILEnv.BedrockCoreEnv.pc ILEnv.BedrockCoreEnv.st
         ILEnv.bedrock_type_W ILEnv.bedrock_type_nat
         ILEnv.bedrock_type_setting_X_state
         ILEnv.bedrock_type_state
         ILEnv.bedrock_type_test
         ILEnv.bedrock_type_reg

         ILEnv.test_seq
         ILEnv.reg_seq
         ILEnv.W_seq

         ILEnv.word_nat_r
         ILEnv.word_state_r
         ILEnv.word_test_r
         
         ILEnv.wplus_r
         ILEnv.wminus_r
         ILEnv.wmult_r
         ILEnv.word_test_r
         ILEnv.wcomparator_r
         ILEnv.Regs_r
         ILEnv.wlt_r
         ILEnv.natToW_r
             
         (** Env **)
         Env.repr_combine Env.default Env.footprint Env.repr'
         Env.updateAt Env.nil_Repr Env.repr Env.updateAt
         Env.repr_combine Env.footprint Env.default Env.repr

         (** Expr **)
         Expr.Range Expr.Domain Expr.Denotation Expr.Impl
         Expr.exists_subst Expr.forallEach Expr.existsEach
         Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
         Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
         Expr.tvar_rec Expr.tvar_rect Expr.liftExpr Expr.lookupAs Expr.Eqb
         Expr.Provable Expr.tvar_val_seqb
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs Expr.AllProvable Expr.AllProvable_gen
         Expr.Provable Expr.tvarD
         Expr.expr_seq_dec
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs 
         Expr.tvarD Expr.Eqb
         Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
         Expr.Default_signature Expr.EmptySet_type Expr.Impl Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
         Expr.expr_seq_dec  Expr.expr_seq_dec
         Expr.tvar_val_seqb  Expr.liftExpr Expr.exprSubstU
         Expr.typeof
         Expr.Impl_ Expr.exprD
         Expr.expr_ind
         Expr.expr_seq_dec
         Expr.get_Eq
         Expr.const_seqb
         Expr.tvar_seqb
         Expr.tvar_val_seqb_correct
         Expr.tvar_seqb_correct
         Expr.mentionsU
         ReifyExpr.default_type


         (** ExprUnify **)
         U.exprUnify U.exprUnify_recursor
         U.exprInstantiate U.subst_exprInstantiate
         U.Subst_lookup U.subst_lookup
         U.Subst_empty U.subst_empty
         U.Subst_set U.subst_set
         U.Subst_equations
         U.Subst_size
         U.dep_in
         U.exprUnify_recursor

         U.FM.Raw.height U.FM.Raw.cardinal U.FM.Raw.assert_false U.FM.Raw.create
         U.FM.Raw.bal U.FM.Raw.remove_min U.FM.Raw.merge U.FM.Raw.join
         U.FM.Raw.t_left U.FM.Raw.t_opt U.FM.Raw.t_right
         U.FM.Raw.cardinal U.FM.Raw.empty U.FM.Raw.is_empty
         U.FM.Raw.mem U.FM.Raw.find   
         U.FM.Raw.add  U.FM.Raw.remove
         U.FM.Raw.fold U.FM.Raw.map U.FM.Raw.mapi U.FM.Raw.map2

         U.FM.this U.FM.is_bst
         U.FM.empty U.FM.is_empty
         U.FM.add U.FM.remove
         U.FM.mem U.FM.find
         U.FM.map U.FM.mapi U.FM.map2
         U.FM.elements U.FM.cardinal U.FM.fold
         U.FM.equal
         U.FM.E.eq_dec

         (** Unfolder **)
         Unfolder.FM.empty Unfolder.FM.add Unfolder.FM.remove
         Unfolder.FM.fold Unfolder.FM.map
         Unfolder.FM.find 
         UNF.LEM.Foralls UNF.Vars
         UNF.UVars UNF.Heap UNF.LEM.Hyps UNF.LEM.Lhs UNF.LEM.Rhs
         UNF.Forward UNF.forward UNF.unfoldForward UNF.Backward
         UNF.backward UNF.unfoldBackward  equiv_dec 
         UNF.find UNF.findWithRest UNF.findWithRest' 
         Folds.allb 
         UNF.openForUnification 
         UNF.quant
         UNF.liftInstantiate
         UNF.applySHeap
         UNF.find UNF.default_hintsPayload
         UNF.applicable UNF.checkAllInstantiated

         (** NatMap **)
         NatMap.singleton
         NatMap.IntMap.Raw.height NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.assert_false NatMap.IntMap.Raw.create
         NatMap.IntMap.Raw.bal NatMap.IntMap.Raw.remove_min NatMap.IntMap.Raw.merge NatMap.IntMap.Raw.join
         NatMap.IntMap.Raw.t_left NatMap.IntMap.Raw.t_opt NatMap.IntMap.Raw.t_right
         NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.empty NatMap.IntMap.Raw.is_empty
         NatMap.IntMap.Raw.mem NatMap.IntMap.Raw.find   
         NatMap.IntMap.Raw.add  NatMap.IntMap.Raw.remove
         NatMap.IntMap.Raw.fold NatMap.IntMap.Raw.map NatMap.IntMap.Raw.mapi NatMap.IntMap.Raw.map2

         NatMap.IntMap.this NatMap.IntMap.is_bst
         NatMap.IntMap.empty NatMap.IntMap.is_empty
         NatMap.IntMap.add NatMap.IntMap.remove
         NatMap.IntMap.mem NatMap.IntMap.find
         NatMap.IntMap.map NatMap.IntMap.mapi NatMap.IntMap.map2
         NatMap.IntMap.elements NatMap.IntMap.cardinal NatMap.IntMap.fold
         NatMap.IntMap.equal
        
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
         Prover.Prove Prover.Prover Prover.Facts Prover.Learn Prover.Summarize
         Prover.composite_ProverT

         (** Provers **)
         Provers.ComboProver

         (** TransitivityProver **)
         provers.TransitivityProver.transitivitySummarize 
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.transitivityProve
         provers.TransitivityProver.groupsOf 
         provers.TransitivityProver.addEquality
         provers.TransitivityProver.proveEqual
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.inSameGroup 
         provers.TransitivityProver.in_seq 
         provers.TransitivityProver.groupWith
         provers.TransitivityProver.transitivityProver

         (** AssumptionProver **)
         provers.AssumptionProver.assumptionProver 
         provers.AssumptionProver.assumptionSummarize
         provers.AssumptionProver.assumptionLearn
         provers.AssumptionProver.assumptionProve

         (** ReflexivityProver **)
         provers.ReflexivityProver.reflexivityProver 
         provers.ReflexivityProver.reflexivitySummarize
         provers.ReflexivityProver.reflexivityLearn
         provers.ReflexivityProver.reflexivityProve

         (** WordProver **)
         provers.WordProver.wordProver provers.WordProver.Source provers.WordProver.Destination provers.WordProver.Difference
         provers.WordProver.pow32 provers.WordProver.wplus' provers.WordProver.wneg' provers.WordProver.wminus' wordBin NToWord Nplus minus
         provers.WordProver.decompose combine Expr.expr_seq_dec provers.WordProver.combineAll provers.WordProver.combine app
         provers.WordProver.alreadyCovered provers.WordProver.alreadyCovered' andb orb provers.WordProver.merge provers.WordProver.wordLearn1 provers.WordProver.wordLearn
         provers.WordProver.equalitysEq ILEnv.W_seq weq provers.WordProver.equalityMatches provers.WordProver.wordProve provers.WordProver.wordSummarize
         provers.WordProver.types ILEnv.bedrock_type_W provers.WordProver.zero Bool.bool_dec wzero' posToWord bool_rec bool_rect
         Nminus wordToN Nsucc Nmult Pos.mul Pos.add Pos.sub_mask Pos.succ_double_mask Pos.double_mask Pos.pred_double
         provers.WordProver.natToWord' mod2 Div2.div2 whd wtl Pos.double_pred_mask
         provers.WordProver.Equalities provers.WordProver.LessThans provers.WordProver.NotEquals
         provers.WordProver.lessThanMatches

         (** Induction **)
         list_ind list_rec list_rect 
         sumbool_rect sumbool_rec
         sumor_rec sumor_rect 
         nat_rec nat_rect nat_ind
         eq_rect_r eq_rec_r eq_rec eq_rect
         eq_sym f_equal 
         nat_rect eq_ind eq_rec eq_rect
         eq_rec_r eq_rect eq_rec nat_rec nat_rect
         sumbool_rec sumbool_rect
         sumbool_rec sumbool_rect
         sumor_rec sumor_rect
         nat_rec nat_rect

         (** Comparisons **)
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_eq_lt_dec
         Peano_dec.eq_nat_dec
         EquivDec_nat  equiv_dec seq_dec
         nat_eq_eqdec
         EquivDec_SemiDec
         Compare_dec.nat_compare
         NPeano.leb NPeano.ltb

         (** SepExpr **)
         SEP.SDomain SEP.SDenotation 
         SEP.Default_predicate
         SEP.himp SEP.sexprD
         SEP.heq
         nat_eq_eqdec
         SEP.liftSExpr

         (** SepHeap **)
         SH.impures SH.pures SH.other
         SH.liftSHeap SH.sheapSubstU
         SH.starred SH.hash 
         SH.star_SHeap 
         SH.SHeap_empty 
         SH.sheapD

         SepHeap.FM.empty
         SepHeap.FM.map
         SepHeap.FM.find
         SepHeap.FM.add 
         SepHeap.FM.remove 
         SepHeap.FM.fold

         (** SepCancel **)
         CANCEL.sepCancel 
         CANCEL.expr_count_meta CANCEL.expr_size CANCEL.meta_order_funcs CANCEL.meta_order_args
         CANCEL.order_impures 
         CANCEL.cancel_in_order
         CANCEL.unify_remove CANCEL.unifyArgs
         
         (** Ordering **)
         Ordering.insert_in_order Ordering.list_lex_cmp Ordering.sort
         
         (** Multimaps **)
         SepHeap.MM.mmap_add SepHeap.MM.mmap_extend SepHeap.MM.mmap_join
         SepHeap.MM.mmap_mapi SepHeap.MM.mmap_map
         SepHeap.MM.empty

         (** PtsTo Plugin **)
         Plugin_PtsTo.ptsto32_ssig 
         Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
         Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
         Plugin_PtsTo.types 
         Plugin_PtsTo.MemEval_ptsto32
         Plugin_PtsTo.MemEvaluator_ptsto32

         (** General Recursion **)
         Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
         GenRec.guard Acc_rect well_founded_ind 
         well_founded_induction_type Acc_inv ExprUnify.wf_R_expr  

         (** Folds **)
         Folds.fold_left_2_opt Folds.fold_left_3_opt

         (** List Functions **)
         tl hd_error value error hd
         nth_error Datatypes.length fold_right firstn skipn rev
         rev_append List.map app fold_left

         (** Aux Functions **)
         fst snd projT1 projT2 Basics.impl value error 
         projT1 projT2 andb orb
         plus minus
         existsSubst

         (** Reflection **)
         (* Reflection.Reflect_eqb_nat *)

         (** Array *)
         Array.ssig Array.types_r Array.types
         Array.MemEval Array.MemEvaluator
         Array.div4 Array.deref Array.sym_read Array.sym_write
         Array.wlength_r Array.sel_r Array.upd_r

         (** Locals *)
         Locals.bedrock_type_string Locals.bedrock_type_listString Locals.bedrock_type_vals
         Locals.ssig Locals.types_r Locals.types
         Locals.MemEval Locals.MemEvaluator
         Locals.ascii_eq Locals.string_eq Bool.eqb
         Locals.nil_r Locals.cons_r Locals.sel_r Locals.upd_r
         Locals.deref Locals.listIn Locals.sym_sel Locals.sym_read Locals.sym_write
         
         (** ?? **)
         DepList.hlist_hd DepList.hlist_tl
         eq_sym eq_trans
         EqNat.beq_nat

         (** TODO: sort these **)
         ILAlgoTypes.Env ILAlgoTypes.Algos ILAlgoTypes.Algos_correct
         ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Preds ILAlgoTypes.PACK.Funcs
         ILAlgoTypes.PACK.applyTypes
         ILAlgoTypes.PACK.applyFuncs
         ILAlgoTypes.PACK.applyPreds

         ILAlgoTypes.BedrockPackage.bedrock_package
         Env.repr_combine Env.footprint Env.nil_Repr
         Env.listToRepr
         app map
         
         ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r 
         ILAlgoTypes.AllAlgos_composite
         ILAlgoTypes.oplus Prover.composite_ProverT 
         (*TacPackIL.MEVAL.Composite.MemEvaluator_composite*) Env.listToRepr

         Plugin_PtsTo.ptsto32_ssig Bedrock.sep.Array.ssig

       ] in H
  end; refold.


Ltac evaluate ext :=
  repeat match goal with
           | [ H : ?P -> False |- _ ] => change (not P) in H
         end;
  SymILTac.Tactics.sym_eval ltac:(isConst) ext ltac:(hints_ext_simplifier ext).

Ltac cancel ext := sep_canceler ltac:(isConst) ext ltac:(hints_ext_simplifier ext); sep_firstorder.

Ltac unf := unfold substH.
Ltac reduce := Programming.reduce unf.
Ltac ho := Programming.ho unf; reduce.

Theorem implyR : forall pc state specs (P Q R : PropX pc state),
  interp specs (P ---> R)
  -> interp specs (P ---> Q ---> R)%PropX.
  intros.
  do 2 apply Imply_I.
  eapply Imply_E.
  eauto.
  constructor; simpl; tauto.
Qed.

Ltac words := repeat match goal with
                       | [ H : _ = _ |- _ ] => rewrite H
                     end; W_eq.

Definition locals_return ns vs avail p (ns' : list string) (avail' offset : nat) :=
  locals ns vs avail p.

Theorem create_locals_return : forall ns' avail' ns avail offset vs p,
  locals ns vs avail p = locals_return ns vs avail p ns' avail' offset.
  reflexivity.
Qed.

Definition ok_return (ns ns' : list string) (avail avail' offset : nat) :=
  (avail >= avail' + length ns')%nat
  /\ offset = 4 * length ns.

Ltac peelPrefix ls1 ls2 :=
  match ls1 with
    | nil => ls2
    | ?x :: ?ls1' =>
      match ls2 with
        | x :: ?ls2' => peelPrefix ls1' ls2'
      end
  end.

Global Opaque merge.

Ltac step ext := 
  match goal with
    | [ |- _ _ = Some _ ] => solve [ eauto ]
    | [ |- interp _ (![ _ ] _) ] => cancel ext
    | [ |- interp _ (![ _ ] _ ---> ![ _ ] _)%PropX ] => cancel ext
    | [ |- himp _ (locals ?ns'' ?vs _ ?p) (locals ?ns _ ?avail ?p') ] =>
      replace p' with p by words;
      let ns' := peelPrefix ns ns'' in
        apply (@prelude_out ns ns' vs avail p); simpl; omega
    | [ |- himp _ ?pre ?post ] =>
      match post with
        | context[locals ?ns ?vs ?avail _] =>
          match pre with
            | context[locals ?ns' ?vs' ?avail' _] =>
              match vs' with
                | vs => fail 1
                | _ => let offset := eval simpl in (4 * List.length ns) in
                  rewrite (create_locals_return ns' avail' ns avail offset);
                  assert (ok_return ns ns' avail avail' offset)%nat by (split; [
                    simpl; omega
                    | reflexivity ] );
                    solve [ cancel ext ]
              end
          end
      end
    | [ |- himp _ _ _ ] => progress cancel ext
    | [ |- interp _ (_ _ _ ?x ---> _ _ _ ?y ---> _ ?x)%PropX ] =>
      match y with
        | x => fail 1
        | _ => apply implyR
      end
    | _ => ho
  end.

Theorem use_HProp_extensional : forall p, HProp_extensional p
  -> (fun st sm => p st sm) = p.
  auto.
Qed.

Ltac descend := 
  (*TIME time "descend:descend" *)
  Programming.descend; 
  (*TIME time "descend:reduce" *)
  reduce;
  (*TIME time "descend:unfold_simpl" ( *)
  unfold hvarB; simpl
  (*TIME ) *);
  (*TIME time "descend:loop" *)
    (repeat match goal with
             | [ |- context[fun stn0 sm => ?f stn0 sm] ] =>
               rewrite (@use_HProp_extensional f) by auto
             | [ |- context[fun stn0 sm => ?f ?a stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d ?e stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d e)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d ?e ?f stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d e f)) by auto
           end).

Definition locals_call ns vs avail p (ns' : list string) (avail' : nat) (offset : nat) :=
  locals ns vs avail p.

Definition ok_call (ns ns' : list string) (avail avail' : nat) (offset : nat) :=
  (length ns' <= avail)%nat
  /\ (avail' <= avail - length ns')%nat
  /\ NoDup ns'
  /\ offset = 4 * length ns.

Definition excessStack (p : W) (ns : list string) (avail : nat) (ns' : list string) (avail' : nat) :=
  reserved (p ^+ natToW (4 * (length ns + length ns' + avail')))
  (avail - length ns' - avail').

Lemma make_call : forall ns ns' vs avail avail' p offset,
  ok_call ns ns' avail avail' offset
  -> locals_call ns vs avail p ns' avail' offset ===>
  locals ns vs 0 p
  * Ex vs', locals ns' vs' avail' (p ^+ natToW offset)
  * excessStack p ns avail ns' avail'.
  unfold ok_call; intuition; subst; eapply do_call; eauto.
Qed.

Lemma make_return : forall ns ns' vs avail avail' p offset,
  ok_return ns ns' avail avail' offset
  -> (locals ns vs 0 p
    * Ex vs', locals ns' vs' avail' (p ^+ natToW offset)
    * excessStack p ns avail ns' avail')
  ===> locals_return ns vs avail p ns' avail' offset.
  unfold ok_return; intuition; subst; apply do_return; omega || words.
Qed.

Definition locals_in ns vs avail p (ns' : list string) (ns'' : list string) (avail' : nat) :=
  locals ns vs avail p.

Open Scope list_scope.

Definition ok_in (ns : list string) (avail : nat) (ns' ns'' : list string) (avail' : nat) :=
  ns ++ ns' = ns'' /\ (length ns' <= avail)%nat /\ NoDup (ns ++ ns')
  /\ avail' = avail - length ns'.

Theorem init_in : forall ns ns' ns'' vs avail p avail',
  ok_in ns avail ns' ns'' avail'
  -> locals_in ns vs avail p ns' ns'' avail' ===>
  Ex vs', locals ns'' (merge vs vs' ns) avail' p.
  unfold ok_in; intuition; subst; apply prelude_in; auto.
Qed.

Ltac prepare fwd bwd := 
  let the_unfold_tac x := 
    eval unfold empB, injB, injBX, starB, exB, hvarB in x
  in
  ILAlgoTypes.Tactics.Extension.extend the_unfold_tac
    isConst auto_ext' tt tt (make_call, init_in, fwd) (make_return, bwd).

Definition auto_ext : TacPackage.
  prepare tt tt.
Defined.

Ltac slotVariable E :=
  match E with
    | 4 => constr:"0"
    | 8 => constr:"1"
    | 12 => constr:"2"
    | 16 => constr:"3"
    | 20 => constr:"4"
    | 24 => constr:"5"
    | 28 => constr:"6"
    | 32 => constr:"7"
    | 36 => constr:"8"
    | 40 => constr:"9"
  end.

Ltac slotVariables E :=
  match E with
    | Binop (LvReg Rv) (RvLval (LvReg Sp)) Plus (RvImm (natToW _))
      :: Assign (LvMem (Indir Rv (natToW ?slot))) _
      :: ?E' =>
      let v := slotVariable slot in
        let vs := slotVariables E' in
          constr:(v :: vs)
    | _ :: ?E' => slotVariables E'
    | nil => constr:(@nil string)
  end.

Ltac post := 
  (*TIME time "post:propxFo" *)
  propxFo; 
  (*TIME time "post:autorewrite" ( *)
  autorewrite with sepFormula in *
  (*TIME ) *) ;
  unfold substH in *;
  (*TIME time "post:simpl" ( *)
  simpl in *;
    try match goal with
          | [ H : context[locals ?ns ?vs ?avail ?p]
              |- context[locals ?ns' _ ?avail' _] ] =>
            match avail' with
              | avail => fail 1
              | _ =>
                (let ns'' := peelPrefix ns ns' in
                 let exposed := eval simpl in (avail - avail') in
                 let new := eval simpl in (List.length ns' - List.length ns) in
                 match new with
                   | exposed =>
                     let avail' := eval simpl in (avail - List.length ns'') in
                     change (locals ns vs avail p) with (locals_in ns vs avail p ns'' ns' avail') in H;
                       assert (ok_in ns avail ns'' ns' avail')%nat
                         by (split; [
                           reflexivity
                           | split; [simpl; omega
                             | split; [ repeat constructor; simpl; intuition congruence
                               | reflexivity ] ] ])                        
                 end)
                || (let offset := eval simpl in (4 * List.length ns) in
                  change (locals ns vs avail p) with (locals_call ns vs avail p ns' avail' offset) in H;
                  assert (ok_call ns ns' avail avail' offset)%nat
                    by (split; [ simpl; omega
                      | split; [ simpl; omega
                        | split; [ repeat constructor; simpl; intuition congruence
                          | reflexivity ] ] ]))
            end
          | [ _ : evalInstrs _ _ ?E = None, H : context[locals ?ns ?vs ?avail ?p] |- _ ] =>
            let ns' := slotVariables E in
            match ns' with
              | nil => fail 1
              | _ =>
                let ns' := constr:("rp" :: ns') in
                  let offset := eval simpl in (4 * List.length ns) in
                    change (locals ns vs avail p) with (locals_call ns vs avail p ns' 0 offset) in H;
                      assert (ok_call ns ns' avail 0 offset)%nat
                        by (split; [ simpl; omega
                          | split; [ simpl; omega
                            | split; [ repeat constructor; simpl; intuition congruence
                              | reflexivity ] ] ])
            end
        end
  (*TIME ) *).

Ltac sep ext := 
  post; evaluate ext; descend; repeat (step ext; descend).

Ltac sepLemma := unfold Himp in *; simpl; intros; cancel auto_ext.

Ltac sep_auto := sep auto_ext.

Hint Rewrite sel_upd_eq sel_upd_ne using congruence : sepFormula.

Lemma sel_merge : forall vs vs' ns nm,
  In nm ns
  -> sel (merge vs vs' ns) nm = sel vs nm.
  intros.
  generalize (merge_agree vs vs' ns); intro Hl.
  eapply Forall_forall in Hl; eauto.
Qed.

Hint Rewrite sel_merge using (simpl; tauto) : sepFormula.
