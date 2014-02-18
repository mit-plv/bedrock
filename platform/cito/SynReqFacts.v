Require Import CompileStmtSpec.
Require Import StringSet.
Import StringSet.
Require Import FreeVars.
Require Import Notations.

Local Open Scope stmt.

Lemma Subset_syn_req_In : forall x vars temp_size s, syn_req vars temp_size s -> Subset (singleton x) (free_vars s) -> List.In x vars.
  admit.
Qed.

Lemma syn_req_Seq_Seq : forall vars temp_size a b c, syn_req vars temp_size ((a ;; b) ;; c) -> syn_req vars temp_size (a ;; b ;; c).
  admit.
Qed.

Lemma syn_req_Seq : forall vars temp_size a b c, syn_req vars temp_size ((a ;; b) ;; c) -> syn_req vars temp_size (b ;; c).
  admit.
Qed.

Lemma syn_req_If_true : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> syn_req vars temp_size (t ;; k).
  admit.
Qed.

Lemma syn_req_If_false : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> syn_req vars temp_size (f ;; k).
  admit.
Qed.

Require CompileExpr.

Lemma syn_req_If_e : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  admit.
Qed.

Lemma syn_req_While_e : forall vars temp_size e s k, syn_req vars temp_size (Syntax.While e s ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  admit.
Qed.

Lemma syn_req_While : forall vars temp_size e s k, syn_req vars temp_size (Syntax.While e s ;; k) -> syn_req vars temp_size (s ;; Syntax.While e s ;; k).
  admit.
Qed.

Lemma syn_req_Call_f : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> CompileExpr.syn_req vars temp_size f 0.
  admit.
Qed.

Require CompileExprs.

Lemma syn_req_Call_args : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> CompileExprs.syn_req vars temp_size args args 0.
  admit.
Qed.

Require SaveRet.

Lemma syn_req_Call_ret : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> SaveRet.syn_req vars x.
  admit.
Qed.

Lemma syn_req_goodSize : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> goodSize (2 + length args).
  admit.
Qed.