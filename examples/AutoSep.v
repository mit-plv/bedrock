Require Import Bedrock.
Export Bedrock.

(** * Specialize the library proof automation to some parameters useful for basic examples. *)

Import SymIL.
Require Bedrock.sep.PtsTo.

(** Build our memory plugin **)
Module Plugin_PtsTo := Bedrock.sep.PtsTo.BedrockPtsToEvaluator.

Ltac sym_eval_simplifier H :=
  Provers.unfold_transitivityProver H ;
  SymIL.MEVAL.Plugin.unfolder H ;
  SymIL.UnfolderLearnHook.unfolder_simplifier H ;
  cbv delta [ 
    Plugin_PtsTo.MemEval_ptsto32 Plugin_PtsTo.ptsto32_ssig 
    IL_mem_satisfies IL_ReadWord IL_WriteWord
    MEVAL.Plugin.smem_read MEVAL.Plugin.smem_write

    Plugin_PtsTo.expr_equal
    Plugin_PtsTo.sym_read_word_ptsto32 Plugin_PtsTo.sym_write_word_ptsto32

    Plugin_PtsTo.ptsto32_types_r
  ] in H ;
  sym_evaluator H.
  
Ltac the_cancel_simplifier :=
  Provers.unfold_transitivityProver tt ;
  cbv beta iota zeta delta 
    [ ILTac.SEP.CancelSep projT1
      ILTac.SEP.hash ILTac.SEP.hash' ILTac.SEP.sepCancel

      SepExpr.FM.fold

      ExprUnify.Subst

      ILEnv.bedrock_types_r ILEnv.bedrock_types
      app map fold_right nth_error value error

      fst snd

      SepExpr.impures ILTac.SEP.star_SHeap SepExpr.FM.empty ILTac.SEP.liftSHeap
      ILTac.SEP.sheapSubstU ExprUnify.empty_Subst

      SepExpr.pures SepExpr.impures SepExpr.other

      ILTac.SEP.exists_subst ExprUnify.env_of_Subst

      ILTac.SEP.multimap_join SepExpr.FM.add SepExpr.FM.find SepExpr.FM.map
      SepExpr.SDomain SepExpr.SDenotation

      ILTac.SEP.unify_remove_all ILTac.SEP.unify_remove

      ILTac.SEP.unifyArgs
      ExprUnify.fold_left_2_opt ExprUnify.fold_left_3_opt
      Compare_dec.lt_eq_lt_dec nat_rec nat_rect 

      ExprUnify.exprUnify ILTac.SEP.substV length ExprUnify.Subst_lookup ExprUnify.Subst_replace
      Expr.liftExpr Expr.exprSubstU
      Peano_dec.eq_nat_dec EquivDec.equiv_dec
      Expr.EqDec_tvar
      Expr.tvar_rec Expr.tvar_rect
      sumbool_rec sumbool_rect
      eq_rec_r eq_rect eq_rec f_equal eq_sym
      ExprUnify.get_Eq
      Expr.Eq
      EquivDec.nat_eq_eqdec

(*      Provers.in_seq_dec *)
      Expr.typeof 
      Expr.expr_seq_dec
      Expr.tvarD
      Expr.tvar_val_sdec 
      Expr.Range Expr.Domain Expr.Denotation
      Expr.well_typed 
      Expr.all2

      ILTac.SEP.forallEach
      ILTac.SEP.sheapD ILTac.SEP.sexprD
      ILTac.SEP.starred ILTac.SEP.himp
      Expr.Impl Expr.Impl_

      Expr.is_well_typed Expr.exprD Expr.applyD

      orb
      Expr.AllProvable Expr.AllProvable_impl Expr.AllProvable_and Expr.AllProvable_gen Expr.Provable Expr.lookupAs

      EquivDec_nat Peano_dec.eq_nat_dec

      Prover.Prove Prover.Facts Prover.Learn Prover.Summarize
      Provers.in_seq Provers.groupWith
    ].

Ltac vcgen :=
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.

Ltac evaluate hints := 
  let plg := 
    SymIL.PluginEvaluator.composite_eval (Plugin_PtsTo.MemEval_ptsto32_correct, tt) 
  in
  let prv ts fs :=
    constr:(@Provers.transitivityProver_correct ts fs)
  in
  let unfolder :=
    match hints with
      | tt => 
        SymIL.UnfolderLearnHook.unfolder_for (@SymIL.UnfolderLearnHook.UNF.hintsSoundness_default)
      | _ => 
        match type of hints with 
          | forall ts pc st fs ps, SymIL.UnfolderLearnHook.UNF.hintsSoundness _ _ _ _ _ => 
            SymIL.UnfolderLearnHook.unfolder_for hints
          | ?T => 
            fail 1000000 "bad hints passed to evaluate" hints "with type" T
        end
    end
  in
  let ssigs :=
    constr:((ptsto32 nil, tt))
  in
  sym_eval ltac:isConst prv plg unfolder sym_eval_simplifier tt tt ssigs.

Ltac cancel :=
  sep_canceler ltac:(isConst) 
    ltac:(fun ts fs => constr:(@Provers.transitivityProver_correct ts fs))
    the_cancel_simplifier tt.

Ltac unf := unfold substH.
Ltac reduce := Programming.reduce unf.
Ltac ho := Programming.ho unf; reduce.
Ltac step := match goal with
               | [ |- _ _ = Some _ ] => solve [ eauto ]
               | [ |- interp _ (![ _ ] _) ] => cancel
               | [ |- interp _ (![ _ ] _ ---> ![ _ ] _)%PropX ] => cancel
               | _ => ho
             end.
Ltac descend := Programming.descend; reduce.

Ltac sep hints := evaluate hints; descend; repeat (step; descend).
