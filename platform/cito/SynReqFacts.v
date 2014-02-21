Require Import CompileStmtSpec.
Require Import StringSet.
Import StringSet.
Require Import FreeVars.
Require Import Notations.

Local Open Scope stmt.

Lemma Subset_singleton : forall x s,
  Subset (singleton x) s
  -> StringSet.In x s.
  intros.
  apply H.
  apply StringFacts.singleton_iff; auto.
Qed.

Local Hint Resolve Subset_singleton.

Lemma In_to_set' : forall x ls acc,
  In x ls \/ StringSet.In x acc
  -> StringSet.In x (fold_left (fun s e => add e s) ls acc).
  induction ls; simpl; intuition (subst; eauto).
  apply IHls.
  right; apply StringFacts.add_iff; auto.
  apply IHls.
  right; apply StringFacts.add_iff; auto.
Qed.

Lemma In_to_set : forall x ls,
  In x ls
  -> StringSet.In x (SetUtil.to_set ls).
  unfold SetUtil.to_set.
  eauto using In_to_set'.
Qed.

Local Hint Resolve In_to_set.

Lemma to_set_In' : forall x ls acc,
  StringSet.In x (fold_left (fun s e => add e s) ls acc)
  -> In x ls \/ StringSet.In x acc.
  induction ls; simpl; intuition (subst; eauto).
  apply IHls in H; intuition.
  apply StringFacts.add_iff in H0; intuition subst.
Qed.

Lemma to_set_In : forall x ls,
  StringSet.In x (SetUtil.to_set ls)
  -> In x ls.
  unfold SetUtil.to_set.
  intros.
  eapply to_set_In' in H; intuition.
  apply StringFacts.empty_iff in H0; tauto.
Qed.

Local Hint Resolve to_set_In.

Lemma Subset_union_left : forall a b c,
  Subset (StringSet.union a b) c
  -> Subset a c /\ Subset b c.
  unfold Subset; intuition;
    (apply H; apply StringFacts.union_iff; auto).
Qed.

Lemma Subset_union_right : forall a b c,
  Subset a c
  -> Subset b c
  -> Subset (StringSet.union a b) c.
  unfold Subset; intuition.
  apply StringFacts.union_iff in H1; intuition.
Qed.

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
