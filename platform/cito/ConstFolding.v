Require Import Optimizer.
Require Import Syntax Semantics.
Require Import SyntaxExpr.

Set Implicit Arguments.

Definition VarToW := string -> option W.

Fixpoint const_folding_expr (e : Expr) (env : VarToW) : Expr :=
  match e with
    | Var var =>
      match env var with
        | Some w => Const w
        | None => e
      end
    | Const w => e
    | Binop op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match a', b' with
        | Const wa,  Const wb => Const (evalBinop op wa wb)
        | _, _ => Binop op a' b'
      end
    | TestE op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match a', b' with
        | Const wa,  Const wb => Const (if evalTest op wa wb then $1 else $0)
        | _, _ => TestE op a' b'
      end
  end.

Definition Vars := list string.

Open Scope type_scope.

(* Info: vars with know value * assigned vars *)
Definition Info := VarToW * Vars.

Definition empty_Vars : Vars := nil.

Variable subtract : VarToW -> Vars -> VarToW.
Infix "-" := subtract.

Variable union : Vars -> Vars -> Vars.
Infix "+" := union.

Variable add : Vars -> string -> Vars.
Infix "%+" := add (at level 60).

Variable VarToW_add : VarToW -> string * W -> VarToW.
Infix "%%+" := VarToW_add (at level 60).

Variable VarToW_del : VarToW -> string -> VarToW.
Infix "%%-" := VarToW_del (at level 60).

Inductive IsZeroResult := 
  | IsZero : IsZeroResult
  | NotAlwaysZero : Expr -> IsZeroResult.

Definition const_folding_expr_is_zero e env : IsZeroResult :=
  match const_folding_expr e env with
    | Const w =>
      if wneb w $0 then
        NotAlwaysZero (Const w)
      else
        IsZero
    | c' => NotAlwaysZero c'
  end.

Fixpoint const_folding (s : Statement) (info : Info) : Statement * Info :=
  match s with
    | Syntax.Skip => (s, info)
    | Syntax.Seq a b => 
      let (a', info') := const_folding a info in
      let (b', info'') := const_folding b info' in
      (Syntax.Seq a' b', info'')
    | Conditional c t f =>
      match const_folding_expr c (fst info) with
        | Const w =>
          if wneb w $0 then
            const_folding t info
          else
            const_folding f info
        | c' =>
          let (t', info_t) := const_folding t (fst info, empty_Vars) in
          let (f', info_f) := const_folding f (fst info, empty_Vars) in
          (* assigned vars in branches will no longer have known values *)
          let vars_with_known_value := fst info - snd info_t - snd info_f in
          let assigned_vars := snd info + snd info_t + snd info_f in
          (Conditional c' t' f', (vars_with_known_value, assigned_vars))
      end
    | Loop c b =>
      match const_folding_expr_is_zero c (fst info) with
        | IsZero =>
            (Syntax.Skip, info)
        | NotAlwaysZero c' =>
          let (b', info_b) := const_folding b (fst info, empty_Vars) in
          (* assigned vars in loop body will no longer have known values *)
          let vars_with_know_value := fst info - snd info_b in
          let assigned_vars := snd info + snd info_b in
          (Loop c' b', (vars_with_know_value, assigned_vars))
      end          
    | Syntax.Assignment var e =>
      let assigned_vars := snd info %+ var in
      match const_folding_expr e (fst info) with
        | Const w =>
          let vars_with_known_value := fst info %%+ (var, w) in
          (Syntax.Assignment var (Const w), (vars_with_known_value, assigned_vars))
        | e' =>
          let vars_with_known_value := fst info %%- var in
          (Syntax.Assignment var e', (vars_with_known_value, assigned_vars))
      end
    | Syntax.ReadAt var arr idx =>
      let arr' := const_folding_expr arr (fst info) in
      let idx' := const_folding_expr idx (fst info) in
      (Syntax.ReadAt var arr' idx', (fst info %%- var, snd info %+ var))
    | Syntax.WriteAt arr idx e =>
      let arr' := const_folding_expr arr (fst info) in
      let idx' := const_folding_expr idx (fst info) in
      let e' := const_folding_expr e (fst info) in
      (Syntax.WriteAt arr' idx' e', info)
    | Syntax.Len var arr =>
      let arr' := const_folding_expr arr (fst info) in
      (Syntax.Len var arr', (fst info %%- var, snd info %+ var))
    | Syntax.Malloc var size =>
      let size' := const_folding_expr size (fst info) in
      (Syntax.Malloc var size', (fst info %%- var, snd info %+ var))
    | Syntax.Free arr =>
      let arr' := const_folding_expr arr (fst info) in
      (Syntax.Free arr', info)
    | Syntax.Call f x =>
      let f' := const_folding_expr f (fst info) in
      let x' := const_folding_expr x (fst info) in
      (Syntax.Call f' x', info)
  end.

Definition agree_with (v : vals) (m : VarToW) :=
  forall x w,
    m x = Some w ->
    v x = w.

Definition const_folding_rel vs s vt t := 
  exists info,
    t = fst (const_folding s info) /\
    vt = vs /\
    agree_with vs (fst info).

Require Import GeneralTactics.
Require Import StepsTo.

Hint Unfold const_folding_rel.

Require Import WritingPrograms.
Require Import SemanticsExpr.

Lemma expr_dec : 
  forall e, 
    (exists x, e = Var x) \/
    (exists w, e = Const w) \/
    (exists op a b, e = Binop op a b) \/
    (exists op a b, e = TestE op a b).
Proof.
  destruct e.
  left; eexists; intuition eauto.
  right; left; eexists; intuition eauto.
  right; right; left; do 3 eexists; intuition eauto.
  right; right; right; do 3 eexists; intuition eauto.
Qed.

Lemma const_folding_expr_correct : forall e e' m local, e' = const_folding_expr e m -> agree_with local m -> exprDenote e' local = exprDenote e local.
  admit.
Qed.

Lemma agree_with_remove : forall local m x e, agree_with local m -> agree_with (upd local x e) (m %%- x).
  admit.
Qed.
Hint Resolve agree_with_remove.

Lemma agree_with_add : forall local m x w, agree_with local m -> agree_with (upd local x w) (m %%+ (x, w)).
  admit.
Qed.
Hint Resolve agree_with_add.

Lemma assign_done : 
  forall x e info local heap local' heap', 
    let s := x <- e in
    let result := const_folding s info in
    Step (fst result) (local, heap) (Done (local', heap')) ->
    agree_with local (fst info) ->
    Step s (local, heap) (Done (local', heap')) /\
    agree_with local' (fst (snd result)).
Proof.
  intros.
  unfold result, s in *; clear result s.
  simpl in *.
  specialize (expr_dec (const_folding_expr e (fst info))); intros; openhyp; rewrite H1 in *; simpl in *; inversion H; unfold value_v, v0, v1 in *; clear value_v v0 v1; subst; split; try erewrite const_folding_expr_correct; eauto.
  erewrite <- const_folding_expr_correct.
  2 : symmetry; eauto.
  simpl.
  eauto.
  eauto.
Qed.

Theorem const_folding_rel_is_backward_simulation : is_backward_simulation const_folding_rel.
Proof.
  unfold is_backward_simulation.
  intros until s.
  generalize dependent vs.
  induction s; try solve [simpl; intuition]; intros.
  split.
  intros.
  unfold const_folding_rel in *.
  openhyp.
  subst.
  eexists; intuition eauto.
  2 : eexists; intuition eauto.
  eapply assign_done in H0; eauto; openhyp; eauto.
  eapply assign_done in H0; eauto; openhyp; eauto.
  Admitted.

Hint Resolve const_folding_rel_is_backward_simulation.

Definition empty_VarToW : VarToW := fun _ => None.

Definition empty_info := (empty_VarToW, empty_Vars).

Definition constant_folding s := fst (const_folding s empty_info).

Lemma everything_agree_with_empty_map : forall v, agree_with v empty_VarToW.
  unfold agree_with, empty_VarToW; intuition.
Qed.
Hint Resolve everything_agree_with_empty_map.

Theorem constant_folding_is_congruence : forall s v, const_folding_rel v s v (constant_folding s).
  unfold const_folding_rel; intros; eexists; intuition eauto.
Qed.

Theorem constant_folding_is_backward_similar_callee : 
  forall s, is_backward_similar_callee (Internal s) (Internal (constant_folding s)).
  intros; econstructor; eauto; eapply constant_folding_is_congruence.
Qed.