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
  ] in H.

Theorem readOk : moduleOk read.
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
    pick_continuation ltac:(congruence).
    congruence.
    subst. sep_canceler ltac:(isConst) tt.

  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
    pick_continuation ltac:(congruence).
    congruence.
    subst. sep_canceler ltac:(isConst) tt.
Time Qed.
