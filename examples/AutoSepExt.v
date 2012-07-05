Require Import Bedrock.
Export Bedrock.

(** * Specialize the library proof automation to some parameters useful for basic examples. *)

Import TacPackIL.
Require Bedrock.sep.PtsTo.
Require Export Bedrock.sep.Array Bedrock.sep.Locals.
Require Bedrock.provers.LocalsProver.

(** Build our memory plugin **)
Module Plugin_PtsTo := Bedrock.sep.PtsTo.BedrockPtsToEvaluator.

Definition TacPackage : Type := 
  @ILAlgoTypes.TypedPackage.

(*Import Env ILAlgoTypes Expr ILEnv.
Check (let prover := Bedrock.provers.LocalsProver.LocalsProver in
  let env :=
    {| PACK.Types := Prover.ProverTypes prover
      ; PACK.Funcs := fun ts => Prover.ProverFuncs prover (repr bedrock_types_r ts)
        ; PACK.Preds := fun ts =>
          nil_Repr (SEP.Default_predicate (repr (Prover.ProverTypes prover) (repr bedrock_types_r ts)) (tvType 0) (tvType 1))
    |}
    in
    let algos ts :=
      @Build_AllAlgos (PACK.applyTypes env ts)
      (Some (Prover.Prover prover (PACK.applyTypes env ts)))
      None
      None
      in
      {| Env := env
        ; Algos := algos
        ; Algos_correct := fun ts fs ps =>
          let types := repr (PACK.Types env) (repr bedrock_types_r ts) in
            let funcs := repr (PACK.Funcs env types) fs in
              @Build_AllAlgos_correct types funcs ps (algos ts)
              (@Prover.Prover_correct prover types funcs)
              I I
      |}).*)

Definition auto_ext' : TacPackage.
  ILAlgoTypes.Tactics.build_prover_pack Provers.ComboProver ltac:(fun a =>
  ILAlgoTypes.Tactics.build_prover_pack Bedrock.provers.LocalsProver.LocalsProver ltac:(fun b => 
  ILAlgoTypes.Tactics.build_mem_pack Plugin_PtsTo.ptsto32_pack ltac:(fun c =>
  ILAlgoTypes.Tactics.build_mem_pack Bedrock.sep.Array.pack ltac:(fun d =>
  ILAlgoTypes.Tactics.build_mem_pack Bedrock.sep.Locals.pack ltac:(fun e =>
    ILAlgoTypes.Tactics.glue_packs (ILAlgoTypes.BedrockPackage.bedrock_package, a, b, c, d, e) ltac:(fun res => 
      let res := 
        eval cbv beta iota zeta delta [
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

          Plugin_PtsTo.ptsto32_ssig Bedrock.sep.Array.ssig Bedrock.sep.Locals.ssig

          Bedrock.sep.Locals.types_r Bedrock.sep.Locals.funcs_r
        ] in res in
        ILAlgoTypes.Tactics.opaque_pack res) || fail 1000 "compose" ))))).
Defined.
