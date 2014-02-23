Require Import CompileStmtSpec.
Require Import StringSet.
Import StringSet.
Require Import FreeVars.
Require Import Notations.
Require Import SynReqFactsUtil.

Local Open Scope stmt.

Local Hint Resolve Subset_singleton.
Local Hint Resolve In_to_set.
Local Hint Resolve to_set_In.
Local Hint Resolve Subset_union_right Max.max_lub.

Require CompileExpr CompileExprs SaveRet.

Ltac t := unfold syn_req, CompileExpr.syn_req, CompileExprs.syn_req, SaveRet.syn_req,
  in_scope, WellFormed.wellformed;
  simpl; intuition;
    repeat (match goal with
              | [ H : Subset _ _ |- _ ] => apply Subset_union_left in H
              | [ H : (max _ _ <= _)%nat |- _ ] =>
                generalize (Max.max_lub_l _ _ _ H);
                  generalize (Max.max_lub_r _ _ _ H);
                    clear H
              | [ H : WellFormed.args_not_too_long _ |- _ ] => inversion_clear H; []
              | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E
            end; intuition).

Local Hint Constructors WellFormed.args_not_too_long.

Lemma Subset_syn_req_In : forall x vars temp_size s, syn_req vars temp_size s -> Subset (singleton x) (free_vars s) -> List.In x vars.
  t.
Qed.

Lemma syn_req_Seq_Seq : forall vars temp_size a b c, syn_req vars temp_size ((a ;; b) ;; c) -> syn_req vars temp_size (a ;; b ;; c).
  t.
Qed.

Lemma syn_req_Seq : forall vars temp_size a b c, syn_req vars temp_size ((a ;; b) ;; c) -> syn_req vars temp_size (b ;; c).
  t.
Qed.

Lemma syn_req_If_true : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> syn_req vars temp_size (t ;; k).
  t.
Qed.

Lemma syn_req_If_false : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> syn_req vars temp_size (f ;; k).
  t.
Qed.

Lemma syn_req_If_e : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  t.
Qed.

Lemma syn_req_While_e : forall vars temp_size e s k, syn_req vars temp_size (Syntax.While e s ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  t.
Qed.

Lemma syn_req_While : forall vars temp_size e s k, syn_req vars temp_size (Syntax.While e s ;; k) -> syn_req vars temp_size (s ;; Syntax.While e s ;; k).
  t.
Qed.

Lemma syn_req_Call_f : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> CompileExpr.syn_req vars temp_size f 0.
  t.
Qed.

Local Hint Resolve Max.le_max_l Max.le_max_r.

Lemma max_more : forall n m k,
  (n <= m)%nat
  -> (n <= max m k)%nat.
  intros; transitivity m; eauto.
Qed.

Local Hint Resolve max_more.

Lemma args_bound' : forall x args acc,
  In x args \/ (DepthExpr.depth x <= acc)%nat
  -> (DepthExpr.depth x <= fold_left max (map DepthExpr.depth args) acc)%nat.
  induction args; simpl; intuition (subst; auto).
Qed.

Lemma args_bound : forall args,
  List.Forall (fun e => (DepthExpr.depth e <= CompileExprs.depth args)%nat) args.
  intros; apply Forall_forall; intros; apply args_bound'; auto.
Qed.

Local Hint Resolve args_bound.

Lemma syn_req_Call_args : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> CompileExprs.syn_req vars temp_size args args 0.
  t.
Qed.

Lemma syn_req_Call_ret : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> SaveRet.syn_req vars x.
  t.
Qed.

Lemma syn_req_goodSize : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> goodSize (2 + length args).
  t.
Qed.

Require SetFacts.

Lemma syn_req_Seq_Skip : forall vars temp_size s, syn_req vars temp_size s -> syn_req vars temp_size (s ;; skip).
  t.
  SetFacts.subset_solver; eauto.
Qed.
