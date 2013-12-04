Require Import CompileStmtSpec.
Require Import StringSet.
Require Import FreeVars.
Require Import Notations.

Local Open Scope stmt.

Lemma Subset_in_scope_In : forall x vars temp_size s, in_scope vars temp_size s -> Subset (singleton x) (free_vars s) -> List.In x vars.
  admit.
Qed.

Lemma in_scope_Seq_Seq : forall vars temp_size a b c, in_scope vars temp_size ((a ;; b) ;; c) -> in_scope vars temp_size (a ;; b ;; c).
  admit.
Qed.

Lemma in_scope_Seq : forall vars temp_size a b c, in_scope vars temp_size ((a ;; b) ;; c) -> in_scope vars temp_size (b ;; c).
  admit.
Qed.

Lemma in_scope_If_true : forall vars temp_size e t f k, in_scope vars temp_size (Syntax.If e t f ;; k) -> in_scope vars temp_size (t ;; k).
  admit.
Qed.

Lemma in_scope_If_false : forall vars temp_size e t f k, in_scope vars temp_size (Syntax.If e t f ;; k) -> in_scope vars temp_size (f ;; k).
  admit.
Qed.