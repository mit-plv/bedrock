Require Import CompileStmtSpec.
Require Import StringSet.
Require Import FreeVars.
Require Import Notations.

Local Open Scope stmt.

Lemma syn_req_Label_in : forall vars temp_size x lbl k, syn_req vars temp_size (Syntax.Label x lbl ;; k) -> List.In x vars.
  admit.
Qed.

Lemma syn_req_Assign_in : forall vars temp_size x e k, syn_req vars temp_size (Syntax.Assign x e ;; k) -> List.In x vars.
  admit.
Qed.

