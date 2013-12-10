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

Require CompileExpr.

Lemma in_scope_If_e : forall vars temp_size e t f k, in_scope vars temp_size (Syntax.If e t f ;; k) -> CompileExpr.in_scope vars temp_size e 0.
  admit.
Qed.

Lemma in_scope_While_e : forall vars temp_size e s k, in_scope vars temp_size (Syntax.While e s ;; k) -> CompileExpr.in_scope vars temp_size e 0.
  admit.
Qed.

Lemma in_scope_While : forall vars temp_size e s k, in_scope vars temp_size (Syntax.While e s ;; k) -> in_scope vars temp_size (s ;; Syntax.While e s ;; k).
  admit.
Qed.

Lemma in_scope_Call_f : forall vars temp_size x f args k, in_scope vars temp_size (Syntax.Call x f args ;; k) -> CompileExpr.in_scope vars temp_size f 0.
  admit.
Qed.

Require CompileExprs.

Lemma in_scope_Call_args : forall vars temp_size x f args k, in_scope vars temp_size (Syntax.Call x f args ;; k) -> CompileExprs.in_scope vars temp_size args 0.
  admit.
Qed.

Require SaveRet.

Lemma in_scope_Call_ret : forall vars temp_size x f args k, in_scope vars temp_size (Syntax.Call x f args ;; k) -> SaveRet.in_scope vars x.
  admit.
Qed.