Require Import Optimizer.
Require Import Syntax Semantics.
Require Import SyntaxExpr.
Require Import GeneralTactics.
Require Import StepsTo.
Require Import WritingPrograms.
Require Import SemanticsExpr.

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

Hypothesis sel_remove_eq : forall m x, (m %%- x) x = None.

Hypothesis sel_remove_ne : forall m x x', x <> x' -> (m %%- x) x' = m x'.

Hypothesis sel_add_eq : forall m x w, (m %%+ (x, w)) x = Some w.

Hypothesis sel_add_ne : forall m x w x', x <> x' -> (m %%+ (x, w)) x' = m x'.

Definition const_dec : forall e, {w | e = Const w} + {~ exists w, e = Const w}.
  intros; destruct e; solve [ right; intuition; openhyp; intuition | left; eauto ].
Qed.

Definition const_zero_dec : forall e, {e = Const $0} + {e <> Const $0}.
  intros; destruct e; solve [right; intuition | destruct (weq w $0); intuition ].
Qed.

Notation "{ x }" := (x :: nil).

Notation "'skip'" := Syntax.Skip.

Fixpoint const_folding (s : Statement) (map : VarToW) : Statement * VarToW * Vars :=
  match s with
    | Syntax.Skip => (skip, map, nil)
    | a ;; b => 
      let result_a := const_folding a map in
      let map' := snd (fst result_a) in
      let result_b := const_folding b map' in
      let a' := fst (fst result_a) in
      let b' := fst (fst result_b) in
      let map'' := snd (fst result_b) in
      let written_a := snd result_a in
      let written_b := snd result_b in
      (a' ;; b', map'', written_a + written_b)
    | x <- e =>
      let e' := const_folding_expr e map in 
      match const_dec e' with
        | inleft (exist w _) =>
          let map' := map %%+ (x, w) in
          (x <- w, map', {x})
        | inright _ =>
          let map' := map %%- x in
          (x <- e', map', {x})
      end
    | Conditional c t f =>
      let c' := const_folding_expr c map in 
      match const_dec c' with
        | inleft (exist w _) =>
          if wneb w $0 then
            const_folding t map
          else
            const_folding f map
        | inright _ =>
          let result_t := const_folding t map in
          let result_f := const_folding f map in
          let t' := fst (fst result_t) in
          let f' := fst (fst result_f) in
          let written_t := snd result_t in
          let written_f := snd result_f in
          (* written vars in branches will no longer have known values *)
          let map' := map - written_t - written_f in
          (Conditional c' t' f', map', written_t + written_f)
      end
    | Loop c b =>
      let c' := const_folding_expr c map in
      if const_zero_dec c' then
        (skip, map, nil)
      else
        let result_b := const_folding b map in
        let b' := fst (fst result_b) in
        let written_b := snd result_b in
        (* written vars in loop body will no longer have known values *)
        let map' := map - written_b in
        (Loop c' b', map', written_b)
    | x <== arr[idx] =>
      let arr' := const_folding_expr arr map in
      let idx' := const_folding_expr idx map in
      (x <== arr'[idx'], map %%- x, {x})
    | arr[idx] <== e =>
      let arr' := const_folding_expr arr map in
      let idx' := const_folding_expr idx map in
      let e' := const_folding_expr e map in
      (arr'[idx'] <== e', map, nil)
    | Syntax.Len x arr =>
      let arr' := const_folding_expr arr map in
      (Syntax.Len x arr', map %%- x, {x})
    | x <- new size =>
      let size' := const_folding_expr size map in
      (x <- new size', map %%- x, {x})
    | Syntax.Free arr =>
      let arr' := const_folding_expr arr map in
      (Syntax.Free arr', map, nil)
    | Syntax.Call f x =>
      let f' := const_folding_expr f map in
      let x' := const_folding_expr x map in
      (Syntax.Call f' x', map, nil)
  end.

Definition agree_with (v : vals) (m : VarToW) :=
  forall x w,
    m x = Some w ->
    sel v x = w.

Definition sel_dec : forall (m : VarToW) x, {w | m x = Some w} + {m x = None}.
  intros; destruct (m x); intuition eauto.
Defined.

Ltac my_f_equal :=
  match goal with
    | |- (if ?E1 then _ else _) = (if ?E2 then _ else _) => replace E2 with E1; try reflexivity
  end.

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

Lemma const_folding_expr_correct' : 
  forall e e' m local, 
    e' = const_folding_expr e m -> 
    agree_with local m -> 
    exprDenote e' local = exprDenote e local.
Proof.
  induction e; try solve [simpl; intuition]; intros.
  simpl in *.
  destruct (sel_dec m s).
  destruct s0.
  subst; rewrite e.
  simpl.
  unfold agree_with in *.
  symmetry.
  eauto.
  subst; rewrite e.
  eauto.

  simpl in *.
  subst.
  eauto.
  
  simpl in *.
  specialize (expr_dec (const_folding_expr e1 m)); intros; openhyp; subst; rewrite H1 in *.

  simpl in *; f_equal.
  replace (local x) with (exprDenote x local); eauto.
  eauto.

  specialize (expr_dec (const_folding_expr e2 m)); intros; openhyp; subst; rewrite H in *; simpl in *; (f_equal; [ replace x with (exprDenote x local); eauto | ]).
  replace (local x0) with (exprDenote x0 local); eauto.
  replace x0 with (exprDenote x0 local); eauto.
  replace (evalBinop _ _ _) with (exprDenote (Binop x0 x1 x2) local); eauto.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x0 x1 x2) local)
  end; eauto.

  simpl in *; f_equal.
  replace (evalBinop _ _ _) with (exprDenote (Binop x x0 x1) local); eauto.
  eauto.

  simpl in *; f_equal.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x x0 x1) local)
  end; eauto.
  eauto.

  simpl in *.
  specialize (expr_dec (const_folding_expr e1 m)); intros; openhyp; subst; rewrite H1 in *.

  simpl in *; my_f_equal; f_equal.
  replace (local x) with (exprDenote x local); eauto.
  eauto.

  specialize (expr_dec (const_folding_expr e2 m)); intros; openhyp; subst; rewrite H in *; simpl in *; (my_f_equal; f_equal; [ replace x with (exprDenote x local); eauto | ]).
  replace (local x0) with (exprDenote x0 local); eauto.
  replace x0 with (exprDenote x0 local); eauto.
  replace (evalBinop _ _ _) with (exprDenote (Binop x0 x1 x2) local); eauto.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x0 x1 x2) local)
  end; eauto.

  simpl in *; my_f_equal; f_equal.
  replace (evalBinop _ _ _) with (exprDenote (Binop x x0 x1) local); eauto.
  eauto.

  simpl in *; my_f_equal; f_equal.
  match goal with
    | |- ?E = _ => replace E with (exprDenote (TestE x x0 x1) local)
  end; eauto.
  eauto.
Qed.

Lemma const_folding_expr_correct : 
  forall e m local, 
    agree_with local m -> 
    exprDenote (const_folding_expr e m) local = exprDenote e local.
  intros; erewrite const_folding_expr_correct'; eauto.
Qed.

Lemma agree_with_remove : forall local m x e, agree_with local m -> agree_with (upd local x e) (m %%- x).
  unfold agree_with; intros; destruct (string_dec x x0).
  subst; rewrite sel_remove_eq in *; discriminate.
  rewrite sel_remove_ne in *; eauto; rewrite sel_upd_ne; eauto.
Qed.
Hint Resolve agree_with_remove.

Lemma agree_with_add : forall local m x w, agree_with local m -> agree_with (upd local x w) (m %%+ (x, w)).
  unfold agree_with; intros; destruct (string_dec x x0).
  subst.
  rewrite sel_add_eq in *; eauto; injection H0; intros; subst; rewrite sel_upd_eq in *; eauto.
  rewrite sel_add_ne in *; eauto; rewrite sel_upd_ne; eauto.
Qed.
Hint Resolve agree_with_add.

Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Lemma assign_done : 
  forall x e map local heap local' heap', 
    let s := x <- e in
    let result := const_folding s map in
    let s' := fst (fst result) in
    let map' := snd (fst result) in
    Step s' (local, heap) (Done (local', heap')) ->
    agree_with local map ->
    Step s (local, heap) (Done (local', heap')) /\
    agree_with local' map'.
Proof.
  intros; unfold result, s in *; clear result s; simpl in *; destruct (const_dec _); [ destruct s | ]; simpl in *; inversion H; unfold_all; subst; [ rewrite <- e0 in H | ]; erewrite const_folding_expr_correct' in * by eauto; intuition.
  erewrite <- const_folding_expr_correct'.
  2 : symmetry; eauto.
  2 : eauto.
  simpl; eauto.
Qed.
Hint Resolve assign_done.

Lemma break_pair : forall A B (p : A * B), p = (fst p, snd p).
  intros; destruct p; eauto.
Qed.

Variable submap : VarToW -> VarToW -> Prop.

Infix "%<=" := submap (at level 60).

Lemma agree_with_submap : forall local map map', agree_with local map -> map' %<= map -> agree_with local map'.
  admit.
Qed.
Hint Resolve agree_with_submap.

Lemma submap_trans : forall a b c, a %<= b -> b %<= c -> a %<= c.
  admit.
Qed.

Lemma submap_refl : forall map, map %<= map.
  admit.
Qed.
Hint Resolve submap_refl.

Lemma subtract_submap : forall a b, a - b %<= a.
  admit.
Qed.
Hint Resolve subtract_submap.

Lemma subtract_reorder_submap : forall a b c, a - b - c %<= a - c - b.
  admit.
Qed.
Hint Resolve subtract_reorder_submap.

Lemma submap_add : forall m x w, m %<= (m %%+ (x, w)).
  admit.
Qed.
Hint Resolve submap_add.

Lemma subtract_remove_submap : forall m s, m - (s :: nil) %<= (m %%- s).
  admit.
Qed.
Hint Resolve subtract_remove_submap.

Lemma map_bound :
  forall s map,
    let result := const_folding s map in
    let map' := snd (fst result) in
    let written := snd result in
    map - written %<= map'.
Proof.
  induction s; simpl; intuition.

  destruct (const_dec _); [ destruct s0 | ]; simpl in *; eauto using submap_trans.
  simpl in *.
  (*here*)
  eauto using submap_trans.
Qed.
Hint Resolve map_bound.

Inductive FoldConst : Statement -> VarToW -> Statement -> VarToW -> Prop :=
  | OptFull : 
      forall s map, 
        let result := fst (const_folding s map) in
        let s' := fst result in
        let map' := snd result in
        FoldConst s map s' map'
  | OptLess :
      forall s map_in t map_out map_in' map_out',
        FoldConst s map_in t map_out ->
        map_in %<= map_in' ->
        map_out' %<= map_out ->
        FoldConst s map_in' t map_out'
  | OptSeq : 
      forall t1 t2 s1 s2 map map' map'',
        FoldConst s1 map t1 map' ->
        FoldConst s2 map' t2 map'' ->
        FoldConst (s1;;s2) map (t1;;t2) map''.

Definition const_folding_rel vs s vt t := 
  exists map map',
    FoldConst s map t map' /\
    vt = vs /\
    agree_with vs map.

Hint Unfold const_folding_rel.

Hint Constructors FoldConst.

Ltac descend :=
  repeat match goal with
           | [ |- exists x, _ ] => eexists
         end.

Opaque const_folding.

Lemma FoldConst_assign' : 
  forall s map_in t map_out, 
    FoldConst s map_in t map_out -> 
    forall x e,
      s = (x <- e) ->
      exists map_in', 
        let result := fst (const_folding s map_in') in
        let s' := fst result in
        let map_out' := snd result in
        t = s' /\
        map_in' %<= map_in /\ 
        map_out %<= map_out'.
Proof.
  induction 1; simpl; intuition; unfold_all; subst.
  descend; intuition.
  edestruct IHFoldConst; eauto; openhyp; subst.
  descend; intuition eauto; eauto using submap_trans.
Qed.

Lemma FoldConst_assign : 
  forall x e map_in t map_out, 
    let s := x <- e in
    FoldConst s map_in t map_out -> 
    exists map_in', 
      let result := fst (const_folding s map_in') in
      let s' := fst result in
      let map_out' := snd result in
      t = s' /\
      map_in' %<= map_in /\ 
      map_out %<= map_out'.
  intros; unfold_all; eapply FoldConst_assign'; eauto.
Qed.

Lemma FoldConst_seq : 
  forall s1 s2 map t map', 
    FoldConst (s1 ;; s2) map t map' ->
    exists t1 t2 map'',
      t = (t1 ;; t2) /\
      FoldConst s1 map t1 map'' /\
      FoldConst s2 map'' t2 map'.
  admit.
Qed.

Lemma FoldConst_if : 
  forall e tt ff map_in t map_out, 
    let s := If e {tt} else {ff} in
    FoldConst s map_in t map_out -> 
    exists map_in',
      let result := fst (const_folding s map_in') in
      let s' := fst result in
      let map_out' := snd result in
      t = s' /\ 
      map_in' %<= map_in /\ 
      map_out %<= map_out'.
  admit.
Qed.

Lemma FoldConst_read : 
  forall x arr idx map_in t map_out, 
    let s := x <== arr[idx] in
    FoldConst s map_in t map_out -> 
    exists map_in', 
      let result := fst (const_folding s map_in') in
      let s' := fst result in
      let map_out' := snd result in
      t = s' /\ 
      map_in' %<= map_in /\ 
      map_out %<= map_out'.
  admit.
Qed.

Lemma FoldConst_write : 
  forall arr idx e map_in t map_out, 
    let s := arr[idx] <== e in
    FoldConst s map_in t map_out -> 
    exists map_in', 
      let result := fst (const_folding s map_in') in
      let s' := fst result in
      let map_out' := snd result in
      t = s' /\ 
      map_in' %<= map_in /\ 
      map_out %<= map_out'.
  admit.
Qed.

Lemma FoldConst_skip : 
  forall map_in t map_out, 
    FoldConst skip map_in t map_out -> 
    t = skip /\ 
    map_out %<= map_in.
  admit.
Qed.

Transparent const_folding.

Lemma const_folding_rel_is_backward_simulation' :
  forall s t map map',
    FoldConst s map t map' ->
    forall vt,
      agree_with vt map ->
      (forall heap vt' heap',
         Step t (vt, heap) (Done (vt', heap')) ->
         Step s (vt, heap) (Done (vt', heap')) /\
         agree_with vt' map') /\
      (forall heap f x t' vt' heap',
         Step t (vt, heap) (ToCall f x t' (vt', heap')) ->
         exists s',
           Step s (vt, heap) (ToCall f x s' (vt', heap')) /\
           exists map_k map_k',
             FoldConst s' map_k t' map_k' /\
             agree_with vt' map_k /\
             map' %<= map_k').
Proof.
  induction s; try solve [simpl; intuition]; intros.

  (* assign *)
  split; intros; eapply FoldConst_assign in H; simpl in *; eauto; openhyp; subst.
  eapply assign_done in H1; eauto; openhyp; eauto.
  destruct (const_dec _); [ destruct s0 | ]; simpl in *; inversion H1.

  (* read *)
  split; intros; eapply FoldConst_read in H; simpl in *; eauto; openhyp; subst; inversion H1; unfold_all; subst; repeat erewrite const_folding_expr_correct in * by eauto; intuition eauto.

  (* write *)
  split; intros; eapply FoldConst_write in H; simpl in *; eauto; openhyp; subst; inversion H1; unfold_all; subst; repeat erewrite const_folding_expr_correct in * by eauto; intuition eauto.

  (* seq *)
  split; intros; eapply FoldConst_seq in H; eauto; openhyp; subst; inversion H1; subst;
  solve [
      destruct v'; simpl in *; eapply IHs1 in H5; eauto; openhyp; eapply IHs2 in H8; eauto; openhyp; descend; intuition eauto |
      eapply IHs1 in H6; eauto; openhyp; descend; intuition; descend; intuition; eauto ].

  (* skip *)
  split; intros; eapply FoldConst_skip in H; eauto; openhyp; subst; inversion H1; subst; eauto.

  (* if *)
  split.

  intros; eapply FoldConst_if in H; simpl in *; eauto; openhyp; subst; destruct (const_dec _).

  destruct s; destruct (Sumbool.sumbool_of_bool (wneb x0 $0)); erewrite e1 in *; [ eapply IHs1 in H1 | eapply IHs2 in H1 ]; eauto; openhyp; replace x0 with (exprDenote x0 vt) in e1 by eauto; rewrite <- e0 in e1; repeat erewrite const_folding_expr_correct in * by eauto; intuition eauto.

  simpl in *; inversion H1; subst; repeat erewrite const_folding_expr_correct in * by eauto; simpl in *; [ eapply IHs1 in H9 | eapply IHs2 in H9 ]; eauto; openhyp; subst; descend; intuition eauto using submap_trans.

  intros; eapply FoldConst_if in H; simpl in *; eauto; openhyp; subst; destruct (const_dec _).

  destruct s; destruct (Sumbool.sumbool_of_bool (wneb x1 $0)); erewrite e1 in *; [ eapply IHs1 in H1 | eapply IHs2 in H1 ]; eauto; openhyp; replace x1 with (exprDenote x1 vt) in e1 by eauto; rewrite <- e0 in e1; repeat erewrite const_folding_expr_correct in * by eauto; descend; intuition eauto; descend; intuition eauto using submap_trans.

  simpl in *; inversion H1; subst; repeat erewrite const_folding_expr_correct in * by eauto; simpl in *; [ eapply IHs1 in H9 | eapply IHs2 in H9 ]; eauto; openhyp; subst; descend; intuition eauto; descend; intuition eauto using submap_trans.

  admit.
  admit.
  admit.
  admit.
  admit.
Qed.

Lemma FoldConst_refl : forall s map, FoldConst s map s map.
  admit.
Qed.
Hint Resolve FoldConst_refl.

Theorem const_folding_rel_is_backward_simulation : is_backward_simulation const_folding_rel.
Proof.
  unfold is_backward_simulation, const_folding_rel.
  intros.
  openhyp; subst.
  eapply const_folding_rel_is_backward_simulation' in H1; eauto.
  openhyp.
  split.
  intros.
  eapply H0 in H2; openhyp.
  eexists; intuition eauto.
  intros.
  eapply H1 in H2; openhyp.
  do 2 eexists; intuition eauto.
Qed.

Hint Resolve const_folding_rel_is_backward_simulation.

Definition empty_VarToW : VarToW := fun _ => None.

Definition constant_folding s := fst (fst (const_folding s empty_VarToW)).

Lemma everything_agree_with_empty_map : forall v, agree_with v empty_VarToW.
  unfold agree_with, empty_VarToW; intuition.
Qed.
Hint Resolve everything_agree_with_empty_map.

Lemma constant_folding_always_FoldConst : forall s map, exists map', FoldConst s map (constant_folding s) map'.
  admit.
Qed.

Theorem constant_folding_is_congruence : forall s v, const_folding_rel v s v (constant_folding s).
  unfold const_folding_rel; intros; exists empty_VarToW; simpl in *; edestruct constant_folding_always_FoldConst; intuition eauto.
Qed.

Theorem constant_folding_is_backward_similar_callee : 
  forall s, is_backward_similar_callee (Internal s) (Internal (constant_folding s)).
  intros; econstructor; eauto; eapply constant_folding_is_congruence.
Qed.