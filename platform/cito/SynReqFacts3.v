Require Import CompileStmtSpec.
Require Import StringSet.
Require Import FreeVars.
Require Import Notations.

Local Open Scope stmt.

Require CompileExpr.

Lemma syn_req_Assign_e : forall vars temp_size x e k, syn_req vars temp_size (Syntax.Assign x e ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  admit.
Qed.

