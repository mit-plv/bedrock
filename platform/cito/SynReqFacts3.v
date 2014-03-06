Require Import CompileStmtSpec.
Require Import StringSet.
Require Import FreeVars.
Require Import SynReqFactsUtil.

Local Infix ";;" := Syntax.Seq (right associativity, at level 95).

Require CompileExpr.

Lemma syn_req_Assign_e : forall vars temp_size x e k, syn_req vars temp_size (Syntax.Assign x e ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  unfold syn_req, CompileExpr.syn_req, in_scope; simpl; intuition.
  apply Subset_union_left in H; intuition.
  apply Subset_union_left in H0; intuition.
  eauto using Max.max_lub_l.
Qed.
