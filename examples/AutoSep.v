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
(*    Env.nat_in Env.nat_eq_bool *)
    Env.listToRepr
    app
  ] in auto_ext' in
  exact v.
Defined.
    
Ltac sym_eval_simplifier H :=
  Provers.unfold_comboProver H ;
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
  Provers.unfold_comboProver tt ;
  ILTac.cancel_simplifier.

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

Hint Extern 1 => tauto : contradiction.
Hint Extern 1 => congruence : contradiction.

Ltac sep_easy := auto with contradiction.

Ltac sep_firstorder := sep_easy;
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- Logic.ex _ ] => sep_easy; eexists
           | [ |- _ /\ _ ] => split
           | [ |- forall x, _ ] => intro
           | [ |- _ = _ ] => reflexivity
           | [ |- himp _ _ _ ] => reflexivity
         end; sep_easy.

Ltac cancel ext :=
  sep_canceler ltac:(isConst) ext the_cancel_simplifier; sep_firstorder.

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
