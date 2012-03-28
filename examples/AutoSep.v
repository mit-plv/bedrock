Require Import Bedrock.
Export Bedrock.

(** * Specialize the library proof automation to some parameters useful for basic examples. *)

Import SymIL.BedrockEvaluator.
Require Bedrock.sep.PtsTo2.

(** Build our memory plugin **)
Module Plugin_PtsTo := Bedrock.sep.PtsTo2.BedrockPtsToEvaluator SymIL.PLUGIN.

Definition master_plugin types' :=
  let types := Env.repr SymIL.bedrock_types_r types' in
  @PluginEvaluator.Plugin_SymEvaluator types (Expr.tvType 0) (Expr.tvType 1)
  ((0, Plugin_PtsTo.MemEval_ptsto32 _) :: nil).

Definition master_plugin_correct types' (_ _ : Expr.tvar) funcs sfuncs : 
  (forall F, F sfuncs -> F (Plugin_PtsTo.ptsto32_ssig _ :: tl sfuncs)) ->
  SymEvaluator_correct funcs sfuncs (master_plugin types').
Proof.
  simpl in *. intros.
  generalize PluginEvaluator.Plugin_SymEvaluator_correct.
  unfold master_plugin, PluginEvaluator.pcT, PluginEvaluator.stT.
Admitted.

Ltac prover_unfolder H :=
  match H with
    | tt => 
      cbv delta [
        EquivDec_nat
        Provers.transitivityProver
        Provers.transitivity_summary Provers.transitivitySummarize Provers.transitivityLearn Provers.transitivityProve
        Provers.transitivityEqProver
        Provers.in_seq Provers.inSameGroup Provers.eqD_seq
        Provers.groupsOf Provers.groupWith Provers.addEquality
      ]
    | _ => 
      cbv delta [
        EquivDec_nat
        Provers.transitivityProver
        Provers.transitivity_summary Provers.transitivitySummarize Provers.transitivityLearn Provers.transitivityProve
        Provers.transitivityEqProver
        Provers.in_seq Provers.inSameGroup Provers.eqD_seq
        Provers.groupsOf Provers.groupWith Provers.addEquality
      ] in H
  end.

Ltac unfolder H :=
  prover_unfolder H ;
  cbv delta [
    master_plugin PluginEvaluator.Plugin_SymEvaluator
    Plugin_PtsTo.MemEval_ptsto32
    Plugin_PtsTo.sym_read_word_ptsto32
    Plugin_PtsTo.sym_write_word_ptsto32
    Plugin_PtsTo.expr_equal
  ] in H;
  PluginEvaluator.unfolder H.

Ltac the_cancel_simplifier :=
  prover_unfolder tt ;
  cbv beta iota zeta delta 
    [ SepTac.SEP.CancelSep projT1
      SepTac.SEP.hash SepTac.SEP.hash' SepTac.SEP.sepCancel

      SepExpr.FM.fold

      Provers.Learn Provers.Summarize Provers.Prove 
      Provers.transitivityProver

      ExprUnify.Subst

      SymIL.bedrock_types_r SymIL.bedrock_types
      app map fold_right nth_error value error

      fst snd

      SepExpr.impures SepTac.SEP.star_SHeap SepExpr.FM.empty SepTac.SEP.liftSHeap
      SepTac.SEP.sheapSubstU ExprUnify.empty_Subst

      SepExpr.pures SepExpr.impures SepExpr.other

      SepTac.SEP.exists_subst ExprUnify.env_of_Subst

      SepTac.SEP.multimap_join SepExpr.FM.add SepExpr.FM.find SepExpr.FM.map
      SepExpr.SDomain SepExpr.SDenotation

      SepTac.SEP.unify_remove_all SepTac.SEP.unify_remove

      SepTac.SEP.unifyArgs
      ExprUnify.fold_left_2_opt ExprUnify.fold_left_3_opt
      Compare_dec.lt_eq_lt_dec nat_rec nat_rect 

      ExprUnify.exprUnify SepTac.SEP.substV length ExprUnify.Subst_lookup ExprUnify.Subst_replace
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

      SepTac.SEP.forallEach
      SepTac.SEP.sheapD SepTac.SEP.sexprD
      SepTac.SEP.starred SepTac.SEP.himp
      Expr.Impl Expr.Impl_

      Expr.is_well_typed Expr.exprD Expr.applyD

      tvWord

      orb
      SymIL.BedrockEvaluator.pcT SymIL.BedrockEvaluator.stT
    ].

Ltac vcgen :=
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.

Ltac evaluate := 
  let plg ts pcT stT fs ps :=
    constr:(@master_plugin_correct ts pcT stT fs ps (fun _ x => x))
  in
  let prv ts fs :=
    constr:(@Provers.transitivityProver_correct ts fs)
  in
  sym_eval ltac:isConst prv plg idtac unfolder.

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

Ltac sep := evaluate; descend; repeat (step; descend).
