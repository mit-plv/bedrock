Set Implicit Arguments.

Require Import Semantics Safe.
Require Import Notations.
Local Open Scope stmt.

Lemma RunsTo_Seq_Label : 
  forall lbls fs x lbl k vs h v' w, 
    lbls lbl = Some w ->
    RunsTo (lbls, fs) k (Locals.upd vs x w, h) v' ->
    RunsTo (lbls, fs) (Syntax.Label x lbl ;; k) (vs, h) v'.
  admit.
Qed.

Lemma RunsTo_Seq_Assign : 
  forall env x e k vs h v', 
    RunsTo env k (Locals.upd vs x (SemanticsExpr.eval vs e), h) v' ->
    RunsTo env (Syntax.Assign x e ;; k) (vs, h) v'.
  admit.
Qed.

