Require Import Prover Env.
Require Import ILEnv.
Require provers.AssumptionProver.
Require provers.ReflexivityProver.
Require provers.WordProver.
Require provers.ArrayBoundProver.

Set Implicit Arguments.
Set Strict Implicit.

(** * The Combo Prover **)

Definition comboTypes := repr_combine bedrock_types_r sep.Array.types_r.
Definition comboFuncs types' := repr_combine (bedrock_funcs_r (repr comboTypes types'))
  (Array.funcs_r (repr comboTypes types')).

Definition ComboProver : ProverPackage :=
{| ProverTypes := comboTypes
 ; ProverFuncs := comboFuncs
 ; Prover_correct := fun ts fs => composite_ProverT_correct
   (composite_ProverT_correct (provers.AssumptionProver.assumptionProver_correct _)
     (provers.ReflexivityProver.reflexivityProver_correct _))
   (composite_ProverT_correct
     (provers.WordProver.wordProver_correct (types' := repr comboTypes ts) (repr (comboFuncs ts) fs))
     (provers.ArrayBoundProver.boundProver_correct (types' := repr comboTypes ts) (repr (comboFuncs ts) fs)))
|}.
