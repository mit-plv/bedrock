Require Import Prover.
Require Import ILEnv.
Require provers.AssumptionProver.
Require provers.ReflexivityProver.
Require provers.TransitivityProver.
Require provers.WordProver.

Set Implicit Arguments.
Set Strict Implicit.

(** * The Combo Prover **)
Definition ComboProver : ProverPackage :=
{| ProverTypes := bedrock_types_r
 ; ProverFuncs := bedrock_funcs_r
 ; Prover_correct := fun ts fs => composite_ProverT_correct
   (composite_ProverT_correct (provers.AssumptionProver.assumptionProver_correct _)
     (provers.TransitivityProver.transitivityProver_correct _))
   (provers.WordProver.wordProver_correct _)
|}.
