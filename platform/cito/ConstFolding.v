Require Import Syntax Semantics.
Require Import SyntaxExpr.
Require Import GeneralTactics.
Require Import StepsTo.
Require Import WritingPrograms.
Require Import SemanticsExpr.

Set Implicit Arguments.

Variable PartialMap : Set.

Variable sel : PartialMap -> string -> option W.

Variable SET : Set.

Open Scope type_scope.

Variable subtract : PartialMap -> SET -> PartialMap.
Infix "-" := subtract.

Variable union : SET -> SET -> SET.
Infix "+" := union.

Variable add : SET -> string -> SET.
Infix "%+" := add (at level 60).

Variable PartialMap_add : PartialMap -> string * W -> PartialMap.
Infix "%%+" := PartialMap_add (at level 60).

Variable PartialMap_del : PartialMap -> string -> PartialMap.
Infix "%%-" := PartialMap_del (at level 60).

Hypothesis sel_remove_eq : forall m x, sel (m %%- x) x = None.

Hypothesis sel_remove_ne : forall m x x', x <> x' -> sel (m %%- x) x' = sel m x'.

Hypothesis sel_add_eq : forall m x w, sel (m %%+ (x, w)) x = Some w.

Hypothesis sel_add_ne : forall m x w x', x <> x' -> sel (m %%+ (x, w)) x' = sel m x'.

Variable empty_set : SET.

Notation "{}" := empty_set.

Variable singleton_set : string -> SET.

Notation "{ x }" := (singleton_set x).

Notation skip := Syntax.Skip.

Notation delete := Syntax.Free.

Variable empty_map : PartialMap.

Notation "[]" := empty_map.

Definition agree_with (v : vals) (m : PartialMap) :=
  forall x w,
    sel m x = Some w ->
    Locals.sel v x = w.

Definition submap (a b : PartialMap) := forall x w, sel a x = Some w -> sel b x = Some w.

Infix "%<=" := submap (at level 60).

Lemma empty_map_submap : forall m, empty_map %<= m.
  admit.
Qed.
Hint Resolve empty_map_submap.

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

Lemma subtract_submap : forall a b, a - b %<= a.
  admit.
Qed.
Hint Resolve subtract_submap.

Lemma everything_agree_with_empty_map : forall v, agree_with v empty_map.
  admit.
Qed.
Hint Resolve everything_agree_with_empty_map.

Variable agree_except : vals -> vals -> SET -> Prop.

Lemma agree_except_upd : forall local x w, agree_except local (upd local x w) {x}.
  admit.
Qed.
Hint Resolve agree_except_upd.

Lemma agree_except_same : forall local s, agree_except local local s.
  admit.
Qed.
Hint Resolve agree_except_same.

Lemma agree_except_trans : forall m1 m2 m3 s1 s2, agree_except m1 m2 s1 -> agree_except m2 m3 s2 -> agree_except m1 m3 (s1 + s2).
  admit.
Qed.
Hint Resolve agree_except_trans.

Lemma agree_with_agree_except_subtract : forall v1 v2 m s, agree_with v1 m -> agree_except v1 v2 s -> agree_with v2 (m - s).
  admit.
Qed.
Hint Resolve agree_with_agree_except_subtract.

Variable subset : SET -> SET -> Prop.

Infix "%%<=" := subset (at level 60).

Lemma agree_except_incl : forall v1 v2 s s', agree_except v1 v2 s -> s %%<= s' -> agree_except v1 v2 s'.
  admit.
Qed.
Hint Resolve agree_except_incl.

Lemma subset_union_2 : forall a b, a %%<= a + b.
  admit.
Qed.
Hint Resolve subset_union_2.

Lemma subset_union_1 : forall a b, a %%<= b + a.
  admit.
Qed.
Hint Resolve subset_union_1.

Lemma subset_refl : forall s, s %%<= s.
  admit.
Qed.
Hint Resolve subset_refl.

Lemma union_same_subset : forall s, s + s %%<= s.
  admit.
Qed.
Hint Resolve union_same_subset.

Definition option_dec : forall A (x : option A), {a | x = Some a} + {x = None}.
  destruct x; intuition eauto.
Qed.

Definition const_dec : forall e, {w | e = Const w} + {~ exists w, e = Const w}.
  intros; destruct e; solve [ right; intuition; openhyp; intuition | left; eauto ].
Qed.

Definition const_zero_dec : forall e, {e = Const $0} + {e <> Const $0}.
  intros; destruct e; solve [right; intuition | destruct (weq w $0); intuition ].
Qed.

Fixpoint const_folding_expr (e : Expr) (env : PartialMap) : Expr :=
  match e with
    | Var var =>
      match option_dec (sel env var) with
        | inleft (exist w _) => Const w
        | _ => e
      end
    | Const w => e
    | Binop op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match const_dec a', const_dec b' with
        | inleft (exist wa _),  inleft (exist wb _) => Const (evalBinop op wa wb)
        | _, _ => Binop op a' b'
      end
    | TestE op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match const_dec a', const_dec b' with
        | inleft (exist wa _),  inleft (exist wb _) => Const (if evalTest op wa wb then $1 else $0)
        | _, _ => TestE op a' b'
      end
  end.

Fixpoint const_folding (s : Statement) (map : PartialMap) : Statement * PartialMap * SET :=
  match s with
    | Syntax.Skip => (skip, map, {})
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
      if const_zero_dec (const_folding_expr c map) then
        (skip, map, {})
      else
        let c' := const_folding_expr c [] in
        let result_b := const_folding b [] in
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
      (arr'[idx'] <== e', map, {})
    | Syntax.Len x arr =>
      let arr' := const_folding_expr arr map in
      (Syntax.Len x arr', map %%- x, {x})
    | x <- new size =>
      let size' := const_folding_expr size map in
      (x <- new size', map %%- x, {x})
    | Syntax.Free arr =>
      let arr' := const_folding_expr arr map in
      (Syntax.Free arr', map, {})
    | Syntax.Call f x =>
      let f' := const_folding_expr f map in
      let x' := const_folding_expr x map in
      (Syntax.Call f' x', map, {})
  end.

Ltac f_equal' :=
  match goal with
    | |- (if ?E1 then _ else _) = (if ?E2 then _ else _) => replace E2 with E1; try reflexivity
  end.

Ltac openhyp' :=
  repeat match goal with
           | H : context [const_dec ?E] |- _ => destruct (const_dec E)
           | |- context [const_dec ?E] => destruct (const_dec E)
           | H : context [const_zero_dec ?E] |- _ => destruct (const_zero_dec E)
           | |- context [const_zero_dec ?E] => destruct (const_zero_dec E)
           | H : context [option_dec ?E] |- _ => destruct (option_dec E)
           | |- context [option_dec ?E] => destruct (option_dec E)
           | H : context [ { _ | _ } ] |- _ => destruct H
         end.

Lemma const_folding_expr_correct : 
  forall e m local, 
    agree_with local m -> 
    exprDenote (const_folding_expr e m) local = exprDenote e local.
Proof.
  induction e; simpl; intuition; openhyp'; simpl in *; eauto.

  symmetry; eauto.

  f_equal.
  erewrite <- (IHe1 m); eauto.
  erewrite e0; eauto.
  erewrite <- (IHe2 m); eauto.
  erewrite e; eauto.

  f_equal; eauto.

  f_equal; eauto.

  f_equal'; f_equal.
  erewrite <- (IHe1 m); eauto.
  erewrite e0; eauto.
  erewrite <- (IHe2 m); eauto.
  erewrite e; eauto.

  f_equal'; f_equal; eauto.

  f_equal'; f_equal; eauto.
Qed.

Lemma const_folding_expr_correct' : 
  forall e e' m local, 
    e' = const_folding_expr e m -> 
    agree_with local m -> 
    exprDenote e' local = exprDenote e local.
Proof.
  intros; subst; eapply const_folding_expr_correct; eauto.
Qed.

Ltac descend :=
  repeat match goal with
           | [ |- exists x, _ ] => eexists
         end.

Lemma const_folding_expr_submap_const : forall e m w, const_folding_expr e m = Const w -> forall m', m %<= m' -> const_folding_expr e m' = Const w.
  induction e; simpl; intuition; openhyp'; simpl in *; try discriminate.

  eapply H0 in e0.
  rewrite e0 in e.
  injection e; intros; subst.
  eauto.

  eapply H0 in e0.
  rewrite e0 in e.
  discriminate.

  eapply IHe1 in e4; eauto.
  eapply IHe2 in e3; eauto.
  rewrite e0 in e4; injection e4; intros; subst.
  rewrite e in e3; injection e3; intros; subst.
  eauto.

  contradict n.
  descend.
  eauto.

  contradict n.
  descend.
  eauto.

  eapply IHe1 in e4; eauto.
  eapply IHe2 in e3; eauto.
  rewrite e0 in e4; injection e4; intros; subst.
  rewrite e in e3; injection e3; intros; subst.
  eauto.

  contradict n.
  descend.
  eauto.

  contradict n.
  descend.
  eauto.
Qed.
Hint Resolve const_folding_expr_submap_const.

Lemma not_const_zero_submap : forall e m m', const_folding_expr e m <> Const $0 -> m' %<= m -> const_folding_expr e m' <> Const $0.
  intuition eauto.
Qed.
Hint Resolve not_const_zero_submap.

Lemma not_const_zero_empty_map : forall e m, const_folding_expr e m <> Const $0 -> const_folding_expr e empty_map <> Const $0.
  eauto.
Qed.
Hint Resolve not_const_zero_empty_map.

Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Lemma break_pair : forall A B (p : A * B), p = (fst p, snd p).
  intros; destruct p; eauto.
Qed.

Ltac rewrite_expr := repeat erewrite const_folding_expr_correct in * by eauto.

Lemma while_case :
  forall fs t v v',
    RunsTo fs t v v' ->
    forall s c b m,
        let result := const_folding s m in
        let s' := fst (fst result) in
        let m' := snd (fst result) in
        let written := snd result in
        s = Syntax.Loop c b ->
        t = s' ->
        agree_with (fst v) m ->
        (let s := b in
         (* the induction hypothesis from Lemma const_folding_is_backward_simulation' *)

         forall (vs : vals) (heap : arrays) (vs' : vals) 
                (heap' : arrays) (m : PartialMap),
           let result := const_folding s m in
           let s' := fst (fst result) in
           let m' := snd (fst result) in
           let written := snd result in
           RunsTo fs s' (vs, heap) (vs', heap') ->
           agree_with vs m ->
           RunsTo fs s (vs, heap) (vs', heap') /\ 
           agree_with vs' m' /\
           agree_except vs vs' written

        ) ->
        RunsTo fs s v v' /\
        agree_with (fst v') m' /\
        agree_except (fst v) (fst v') written.
Proof.
  induction 1; simpl; intros; unfold_all; subst.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.
  econstructor 9.
  erewrite <- const_folding_expr_correct'.
  2 : symmetry; eauto.
  simpl; eauto.
  simpl; eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; try discriminate.
  injection H3; intros; subst.
  destruct v; simpl in *.
  destruct v'; simpl in *.
  eapply H5 in H0; eauto; openhyp.
  destruct v''; simpl in *.
  edestruct IHRunsTo2; try reflexivity.
  3 : eauto.
  replace (While (const_folding_expr c _) {{fst (fst (const_folding b _))}}) with (fst (fst (const_folding (While (c) {{b}} ) (m - snd (const_folding b []))))) by (simpl in *; openhyp'; [contradict e; eauto | simpl; eauto ]).
  eauto.
  eauto.
  openhyp.
  simpl in *; openhyp'; [ contradict e; eauto | ]; simpl in *.
  rewrite_expr.
  intuition eauto.

  simpl in *; openhyp'; simpl in *; try discriminate.
  injection H1; intros; subst.
  rewrite_expr.
  intuition eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.

  simpl in *; openhyp'; simpl in *; intuition.
Qed.

Lemma const_folding_is_backward_simulation : 
  forall fs s vs heap vs' heap' m, 
    let result := const_folding s m in
    let s' := fst (fst result) in
    let m' := snd (fst result) in
    let written := snd result in
    RunsTo fs s' (vs, heap) (vs', heap') -> 
    agree_with vs m -> 
    RunsTo fs s (vs, heap) (vs', heap') /\
    agree_with vs' m' /\
    agree_except vs vs' written.
Proof.
  induction s;
  match goal with
    | |- context [Syntax.Loop] => solve [intros; split; intros; eapply while_case in H; eauto; openhyp; eauto]
    | |- _ => idtac
  end; simpl; intros.

  openhyp'; simpl in *; inversion H; unfold_all; subst.
  split.
  rewrite <- e0.
  rewrite_expr.
  eauto.
  eauto.

  split.
  rewrite_expr.
  eauto.
  eauto.

  inversion H; unfold_all; subst; rewrite_expr; eauto.

  inversion H; unfold_all; subst; rewrite_expr; eauto.

  inversion H; unfold_all; subst.
  destruct v'; simpl in *.
  eapply IHs1 in H3; eauto; openhyp.
  eapply IHs2 in H6; eauto; openhyp.
  eauto.

  inversion H; unfold_all; subst; rewrite_expr; eauto.

  openhyp'.

  destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
  eapply IHs1 in H; eauto; openhyp.
  replace x with (exprDenote x vs) in e1 by eauto.
  rewrite <- e0 in e1.
  rewrite_expr.
  eauto.
  eapply IHs2 in H; eauto; openhyp.
  replace x with (exprDenote x vs) in e1 by eauto.
  rewrite <- e0 in e1.
  rewrite_expr.
  eauto.

  simpl in *.
  inversion H; unfold_all; subst.
  rewrite_expr.
  eapply IHs1 in H7; eauto; openhyp.
  intuition eauto.
  rewrite_expr.
  eapply IHs2 in H7; eauto; openhyp.
  split; [econstructor 7 | ]; eauto.

  inversion H; unfold_all; subst; rewrite_expr; eauto.

  inversion H; unfold_all; subst; rewrite_expr; eauto.

  inversion H; unfold_all; subst; rewrite_expr; eauto.

  inversion H; unfold_all; subst; rewrite_expr; eauto.
Qed.

Definition constant_folding s := fst (fst (const_folding s empty_map)).

Definition optimizer := constant_folding.

Lemma optimizer_is_backward_simulation : forall fs s v v', RunsTo fs (optimizer s) v v' -> RunsTo fs s v v'.
  intros.
  unfold optimizer, constant_folding in *.
  destruct v; destruct v'.
  eapply const_folding_is_backward_simulation in H; openhyp; eauto.
Qed.

Import Semantics.Safety.

Lemma const_folding_is_safety_preservation : 
  forall fs s vs heap m, 
    let result := const_folding s m in
    let s' := fst (fst result) in
    Safe fs s (vs, heap) ->
    agree_with vs m ->
    Safe fs s' (vs, heap).
Proof.
  induction s.

  Focus 7.
  intros.
  unfold_all.
  eapply 
    (Safe_coind 
       (fun s' v =>
          (exists c b m,
             let s := While (c) {{b}} in
             Safe fs s v /\
             agree_with (fst v) m /\
             (let s := b in
              forall (vs : vals) (heap : arrays) (m : PartialMap),
                Safe fs s (vs, heap) ->
                agree_with vs m -> Safe fs (fst (fst (const_folding s m))) (vs, heap)
             ) /\
             s' = fst (fst (const_folding s m))) \/
          Safe fs s' v
    )); [ .. | left; descend; intuition eauto ]; clear; simpl; intros; openhyp.

  simpl in *; openhyp'; simpl in *; intuition.

  eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  intuition eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  inversion H; subst.
  intuition eauto.
  right; intuition eauto.

  simpl in *; openhyp'; simpl in *; intuition.
  injection H2; intros; subst.
  rewrite_expr.
  inversion H; unfold_all; subst.
  destruct v; simpl in *.
  left.
  repeat split.
  eauto.
  right.
  eauto.

  intros.
  left.
  destruct v'; simpl in *.
  eapply const_folding_is_backward_simulation in H3; eauto; openhyp.
  descend; intuition.
  simpl in *; openhyp'; [ contradict e; eauto | ]; simpl in *.
  eauto.

  right.
  eauto.

  inversion H; unfold_all; subst.
  intuition eauto.
  right.
  intuition eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  eauto.

  simpl in *; openhyp'; simpl in *; intuition.

  inversion H; unfold_all; subst.
  intuition eauto.
  intuition eauto.

  simpl; intros; simpl in *; openhyp'; simpl in *; eauto.

  simpl; intros; inversion H; unfold_all; subst; econstructor; rewrite_expr; eauto.

  simpl; intros; inversion H; unfold_all; subst; econstructor; rewrite_expr; eauto.

  simpl; intros; inversion H; unfold_all; subst.
  econstructor.
  eauto.
  intros.
  destruct v'; simpl in *.
  eapply const_folding_is_backward_simulation in H1.
  openhyp.
  eauto.
  eauto.

  eauto.

  simpl; intros; openhyp'.

  destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
  inversion H; subst.
  eauto.
  erewrite <- const_folding_expr_correct' in H5.
  2 : symmetry; eauto.
  simpl in *.
  intuition.
  eauto.
  inversion H; subst.
  erewrite <- const_folding_expr_correct' in H5.
  2 : symmetry; eauto.
  simpl in *.
  intuition.
  eauto.
  eauto.

  simpl in *.
  inversion H; subst.
  econstructor.
  rewrite_expr.
  eauto.
  eauto.
  econstructor 5.
  rewrite_expr.
  eauto.
  eauto.

  simpl; intros; inversion H; unfold_all; subst; econstructor; rewrite_expr; eauto.

  simpl; intros; inversion H; unfold_all; subst; econstructor; rewrite_expr; eauto.

  simpl; intros; inversion H; unfold_all; subst; econstructor; rewrite_expr; eauto.

  simpl; intros; inversion H; unfold_all; subst.

  econstructor; rewrite_expr; eauto.

  econstructor 14; rewrite_expr; eauto.

  Grab Existential Variables.
  exact "".
  eauto.
Qed.

Lemma optimizer_is_safety_preservation : forall fs s v, Safety.Safe fs s v -> Safety.Safe fs (optimizer s) v.
  intros.
  unfold optimizer, constant_folding in *.
  destruct v.
  eapply const_folding_is_safety_preservation in H; openhyp; eauto.
Qed.

Lemma const_folding_expr_footprint : forall e m, List.incl (SemanticsExprLemmas.varsIn (const_folding_expr e m)) (SemanticsExprLemmas.varsIn e).
Proof.
  induction e; simpl; intuition.

  openhyp'; simpl in *; eauto.
  openhyp'; simpl in *.
  eauto.
  CompileStatement.incl_app_solver.
  eauto.
  eauto.
  CompileStatement.incl_app_solver.
  eauto.
  eauto.
  openhyp'; simpl in *.
  eauto.
  CompileStatement.incl_app_solver.
  eauto.
  eauto.
  CompileStatement.incl_app_solver.
  eauto.
  eauto.
Qed.
Hint Resolve const_folding_expr_footprint.

Lemma const_folding_footprint : forall s m, List.incl (SemanticsLemmas.footprint (fst (fst (const_folding s m)))) (SemanticsLemmas.footprint s).
Proof.
  induction s; simpl; intuition.

  openhyp'; simpl in *; eauto.
  openhyp'; simpl in *.
  destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
  eauto.
  eauto.
  CompileStatement.incl_app_solver.
  eauto.
  eauto.
  eauto.
  openhyp'; simpl in *; eauto.
Qed.

Lemma optimizer_footprint : forall s, List.incl (SemanticsLemmas.footprint (optimizer s)) (SemanticsLemmas.footprint s).
  unfold optimizer, constant_folding; intros; eapply const_folding_footprint.
Qed.

Open Scope nat.

Lemma both_le : forall a b a' b', a <= a' -> b <= b' -> max a b <= max a' b'.
  intros; CompileStatement.max_le_solver; eauto.
Qed.

Lemma const_folding_expr_depth : forall e m, CompileExpr.depth (const_folding_expr e m) <= CompileExpr.depth e.
Proof.
  induction e; simpl; intuition; openhyp'; simpl in *; eauto.
Qed.
Hint Resolve const_folding_expr_depth.

Lemma const_folding_depth : forall s m, CompileStatement.depth (fst (fst (const_folding s m))) <= CompileStatement.depth s.
Proof.
  induction s; simpl; intuition.

  openhyp'; simpl in *; eauto.
  eapply both_le.
  eauto.
  eapply Le.le_n_S.
  eauto.

  openhyp'; simpl in *; eauto.
  destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
  eauto.
  eauto.
  eapply both_le.
  eauto.
  eauto.

  openhyp'; simpl in *; eauto.
  eapply both_le.
  eauto.
  eauto.
Qed.

Lemma optimizer_depth : forall s, CompileStatement.depth (optimizer s) <= CompileStatement.depth s.
  unfold optimizer, constant_folding; intros; eapply const_folding_depth.
Qed.

Definition is_good_optimizer optimizer :=
  (forall fs s v v', RunsTo fs (optimizer s) v v' -> RunsTo fs s v v') /\ 
  (forall fs s v, Safety.Safe fs s v -> Safety.Safe fs (optimizer s) v) /\
  (forall s, List.incl (SemanticsLemmas.footprint (optimizer s)) (SemanticsLemmas.footprint s)) /\
  (forall s, CompileStatement.depth (optimizer s) <= CompileStatement.depth s).

Lemma constant_folding_is_good_optimizer : is_good_optimizer optimizer.
  repeat split.
  eapply optimizer_is_backward_simulation.
  eapply optimizer_is_safety_preservation.
  eapply optimizer_footprint.
  eapply optimizer_depth.
Qed.