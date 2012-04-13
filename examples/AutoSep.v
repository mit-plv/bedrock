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
  SymIL.Package.build_prover_pack Provers.TransitivityProver ltac:(fun a =>
  SymIL.Package.build_mem_pack Plugin_PtsTo.ptsto32_pack ltac:(fun b => 
    SymIL.Package.glue_pack a b ltac:(fun res => refine res) || fail 1000 "compose")).
Defined.

Definition auto_ext : TacPackage.
  let v := eval unfold auto_ext' in auto_ext' in
  let v := eval cbv delta [ 
    Plugin_PtsTo.ptsto32_ssig MEVAL.Composite.MemEvaluator_composite 
    MEVAL.Default.MemEvaluator_default Prover.composite_ProverT Env.nil_Repr ] in v in
  let v := eval simpl in v in
  exact v.
Defined.

Ltac sym_eval_simplifier H :=
  Provers.unfold_transitivityProver H ;
  SymIL.MEVAL.Plugin.unfolder H ;
  SymIL.MEVAL.LearnHookDefault.unfolder H ;
  SymIL.unfolder_simplifier H ;
  cbv delta [ 
    Plugin_PtsTo.MemEval_ptsto32 Plugin_PtsTo.ptsto32_ssig 
    IL_mem_satisfies IL_ReadWord IL_WriteWord
    MEVAL.Plugin.smem_read MEVAL.Plugin.smem_write

    Plugin_PtsTo.expr_equal
    Plugin_PtsTo.sym_read_word_ptsto32 Plugin_PtsTo.sym_write_word_ptsto32

    Plugin_PtsTo.ptsto32_types_r

    MEVAL.Composite.MemEvaluator_composite
    MEVAL.Default.smemeval_read_word_default
    MEVAL.Default.smemeval_write_word_default
    Plugin_PtsTo.types Prover.composite_ProverT
  ] in H ;
  sym_evaluator H.

Ltac the_cancel_simplifier :=
  Provers.unfold_transitivityProver tt ;
  ILTac.cancel_simplifier.
(*
  cbv beta iota zeta delta 
    [ SEP.sepCancel
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

    (* *)
SEP.sepCancel projT1
      SEP.hash SEP.hash' SEP.sepCancel

      SepExpr.FM.fold

      ExprUnify.Subst

      ILEnv.bedrock_types_r ILEnv.bedrock_types
      app map fold_right nth_error value error

      fst snd

      SEP.star_SHeap SepExpr.FM.empty SEP.liftSHeap
      SEP.sheapSubstU ExprUnify.empty_Subst

      SEP.pures SEP.impures SEP.other

      Expr.exists_subst ExprUnify.env_of_Subst

      SEP.multimap_join SepExpr.FM.add SepExpr.FM.find SepExpr.FM.map
      SEP.SDomain SEP.SDenotation

      SEP.unify_remove_all SEP.unify_remove

      SEP.unifyArgs
      ExprUnify.fold_left_2_opt ExprUnify.fold_left_3_opt
      Compare_dec.lt_eq_lt_dec nat_rec nat_rect 

      ExprUnify.exprUnify SEP.substV length ExprUnify.Subst_lookup ExprUnify.Subst_replace
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

      Expr.forallEach
      SEP.sheapD SEP.sexprD
      SEP.starred SEP.himp
      Expr.Impl Expr.Impl_

      Expr.is_well_typed Expr.exprD Expr.applyD

      orb
      Expr.AllProvable Expr.AllProvable_impl Expr.AllProvable_and Expr.AllProvable_gen Expr.Provable Expr.lookupAs

      EquivDec_nat Peano_dec.eq_nat_dec

      Prover.Prove Prover.Facts Prover.Learn Prover.Summarize
      Provers.in_seq Provers.groupWith
    ].
*)

Ltac vcgen :=
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.

Ltac evaluate ext := 
  let simp H :=
    match H with
      | tt => try cbv beta zeta iota delta [ 
        ext
        SymIL.Algos SymIL.Types SymIL.Preds SymIL.MemEval
        SymIL.Prover SymIL.Hints ]
      | _ => try cbv beta zeta iota delta [ 
        ext
        SymIL.Algos SymIL.Types SymIL.Preds SymIL.MemEval
        SymIL.Prover SymIL.Hints ] in H
    end; sym_eval_simplifier H
  in
  sym_eval ltac:(isConst) ext simp.

Ltac cancel ext :=
  sep_canceler ltac:(isConst) auto_ext the_cancel_simplifier.
(*
    ltac:(fun ts fs => constr:(@Provers.transitivityProver_correct ts fs))
    the_cancel_simplifier tt.
*)

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

Ltac sep ext := evaluate ext; descend; repeat (step ext; descend).

Ltac sepLemma := intros; cancel auto_ext.

(** env -> fwd -> bwd -> (hints -> T) -> T **)
Ltac prepare := SymIL.UNF.prepareHints ltac:(fun x => eval unfold starB exB hvarB in x)
  W (settings * state)%type isConst.

Ltac sep_auto := sep auto_ext.

(*
Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st').

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    If (Rv = 0) {
      $[0] <- 0
    } else {
      $[0] <- $[0]
    } ;;
    Rv <- $[0];;
    Goto Rp
  }
}}.

Theorem readOk : moduleOk read.
  vcgen.
  sep auto_ext.
  sep auto_ext.
  sep auto_ext.
  sep auto_ext.
  sep auto_ext.
  sep auto_ext.
  evaluate auto_ext. 
  descend. step. descend. step. descend. step.

  sep auto_ext.
Qed.
*)