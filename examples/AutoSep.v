Require Import Bedrock.

Set Implicit Arguments.

(** * Let's read from memory! *)

Import SymIL.BedrockEvaluator.
Require Import Bedrock.sep.PtsTo2.

Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st').

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    If (Rv = 0) {
      $[0] <- 0
    } else {
      $[0] <- 0
    } ;;
    Rv <- $[0];;
    Goto Rp
  }
}}.

Ltac unfolder H :=
  cbv delta [
    ptsto_evaluator CORRECTNESS READER WRITER DEMO.expr_equal DEMO.types
    DEMO.ptsto32_ssig DEMO.ptrIndex DEMO.wordIndex
    SymEval.fold_args SymEval.fold_args_update
  ] in H;
  sym_evaluator H.

Ltac the_cancel_simplifier :=
  cbv beta iota zeta delta 
    [ SepTac.SEP.CancelSep
      SepTac.SEP.hash SepTac.SEP.hash' SepTac.SEP.sepCancel

      SepExpr.FM.fold

      Provers.eq_summary Provers.eq_summarize Provers.eq_prove 
      Provers.transitivityEqProverRec

      ExprUnify.Subst

      SymIL.bedrock_types SymIL.bedrock_ext
      app map fold_right nth_error value error

      fst snd

      SepExpr.impures SepTac.SEP.star_SHeap SepExpr.FM.empty SepTac.SEP.liftSHeap
      SepTac.SEP.sheapSubstU ExprUnify.empty_Subst

      SepExpr.pures SepExpr.impures SepExpr.other

      SepTac.SEP.exists_subst ExprUnify.env_of_Subst

      SepTac.SEP.multimap_join SepExpr.FM.add SepExpr.FM.find SepExpr.FM.map

      SepTac.SEP.unify_remove_all SepTac.SEP.unify_remove

      SepTac.SEP.unifyArgs
      ExprUnify.fold_left_2_opt
      Compare_dec.lt_eq_lt_dec nat_rec nat_rect 

      ExprUnify.exprUnify SepTac.SEP.substV length
      Expr.liftExpr Expr.exprSubstU
      Peano_dec.eq_nat_dec EquivDec.equiv_dec 
      Expr.EqDec_tvar
      Expr.tvar_rec Expr.tvar_rect
      sumbool_rec sumbool_rect
      eq_rec_r eq_rect eq_rec f_equal eq_sym
      ExprUnify.get_Eq
      Expr.Eq
      EquivDec.nat_eq_eqdec
      Provers.inSameGroup Provers.eqD Provers.eqD_seq Provers.transitivityEqProver
      Provers.groupsOf
      Provers.addEquality
      Provers.in_seq_dec
      Expr.typeof 
      Expr.expr_seq_dec
      Expr.tvarD
      Expr.tvar_val_sdec 
      Provers.groupWith
      Expr.Range Expr.Domain Expr.Denotation
      Expr.well_typed 
      Expr.all2

      SepTac.SEP.forallEach
      SepTac.SEP.sheapD SepTac.SEP.sexprD
      SepTac.SEP.starred SepTac.SEP.himp
      Expr.Impl
      Expr.is_well_typed 
    ].

Theorem readOk : moduleOk read.
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.
  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
    pick_continuation ltac:(congruence). 
    congruence.
    sep_canceler ltac:(isConst) idtac the_cancel_simplifier tt. reflexivity.

  Time sym_eval ltac:(isConst) idtac unfolder (CORRECTNESS ptsto_evaluator) tt tt tt.
    pick_continuation ltac:(congruence). 
    congruence.
    sep_canceler ltac:(isConst) idtac the_cancel_simplifier tt. reflexivity.
Time Qed.
