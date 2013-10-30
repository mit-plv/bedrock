Require Import Optimizer.
Require Import Syntax Semantics.
Require Import SyntaxExpr.
Require Import GeneralTactics.
Require Import StepsTo.
Require Import WritingPrograms.
Require Import SemanticsExpr.

Set Implicit Arguments.

Variable PartialMap : Set.

Variable sel : PartialMap -> string -> option W.

Fixpoint const_folding_expr (e : Expr) (env : PartialMap) : Expr :=
  match e with
    | Var var =>
      match sel env var with
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

Definition const_dec : forall e, {w | e = Const w} + {~ exists w, e = Const w}.
  intros; destruct e; solve [ right; intuition; openhyp; intuition | left; eauto ].
Qed.

Definition const_zero_dec : forall e, {e = Const $0} + {e <> Const $0}.
  intros; destruct e; solve [right; intuition | destruct (weq w $0); intuition ].
Qed.

Variable empty_set : SET.

Notation "{}" := empty_set.

Variable singleton_set : string -> SET.

Notation "{ x }" := (singleton_set x).

Notation skip := Syntax.Skip.

Notation delete := Syntax.Free.

Variable empty_map : PartialMap.

Notation "[]" := empty_map.

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

Definition agree_with (v : vals) (m : PartialMap) :=
  forall x w,
    sel m x = Some w ->
    Locals.sel v x = w.

Definition sel_dec : forall (m : PartialMap) x, {w | sel m x = Some w} + {sel m x = None}.
  intros; destruct (sel m x); intuition eauto.
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

Lemma break_pair : forall A B (p : A * B), p = (fst p, snd p).
  intros; destruct p; eauto.
Qed.

Variable submap : PartialMap -> PartialMap -> Prop.

Infix "%<=" := submap (at level 60).

Lemma agree_with_submap : forall local map map', agree_with local map -> map' %<= map -> agree_with local map'.
  admit.
Qed.
Hint Resolve agree_with_submap.

Lemma submap_trans : forall a b c, a %<= b -> b %<= c -> a %<= c.
  admit.
Qed.

Lemma subtract_submap : forall a b, a - b %<= a.
  admit.
Qed.
Hint Resolve subtract_submap.

Lemma submap_add : forall m x w, m %<= (m %%+ (x, w)).
  admit.
Qed.
Hint Resolve submap_add.

Lemma submap_refl : forall map, map %<= map.
  admit.
Qed.
Hint Resolve submap_refl.

Lemma subtract_reorder_submap : forall a b c, a - b - c %<= a - c - b.
  admit.
Qed.
Hint Resolve subtract_reorder_submap.

Lemma subtract_remove_submap : forall m s, m - singleton_set s %<= (m %%- s).
  admit.
Qed.
Hint Resolve subtract_remove_submap.

Lemma subtract_union_submap : forall a b c, a - (b + c) %<= a - b - c.
  admit.
Qed.
Hint Resolve subtract_union_submap.

Lemma submap_subtract_submap : forall a b a', a %<= a' -> a - b %<= a' - b.
  admit.
Qed.
Hint Resolve submap_subtract_submap.

Lemma out_map_lower_bound :
  forall s map,
    let result := const_folding s map in
    let map' := snd (fst result) in
    let written := snd result in
    map - written %<= map'.
Proof.
  induction s; simpl; intuition.

  destruct (const_dec _); [ destruct s0 | ]; simpl in *; eauto using submap_trans.
  simpl in *; eauto using submap_trans.
  destruct (const_dec _); [ destruct s; destruct (Sumbool.sumbool_of_bool (wneb x $0)); erewrite e1 in * | ]; simpl in *; eauto using submap_trans.
  destruct (const_zero_dec _); simpl in *; eauto using submap_trans.
Qed.
Hint Resolve out_map_lower_bound.

Variable disjoint : PartialMap -> SET -> Prop.

Infix "%*" := disjoint (at level 60).

Inductive FoldConst : Statement -> PartialMap -> Statement -> PartialMap -> SET -> Prop :=
  | OptFull : 
      forall s map, 
        let result := const_folding s map in
        let s' := fst (fst result) in
        let map' := snd (fst result) in
        let written := snd result in
        FoldConst s map s' map' written
  | OptLess :
      forall s map_in t map_out written map_in' map_out',
        FoldConst s map_in t map_out written ->
        map_in %<= map_in' ->
        map_out' %<= map_out ->
        FoldConst s map_in' t map_out' written
  | OptSeq : 
      forall s1 s2 t1 t2 written1 written2 map map' map'',
        FoldConst s1 map t1 map' written1 ->
        FoldConst s2 map' t2 map'' written2 ->
        FoldConst (s1;;s2) map (t1;;t2) map'' (written1 + written2)
  | OptConsumeBefore :
      forall s1 s2 t1 t2 written1 written2 map1 map1' map2 map2' map_in,
        FoldConst s1 map1 t1 map1' written1 ->
        FoldConst s2 map2 t2 map2' written2 ->
        map1 %<= map_in ->
        map2 %<= map_in ->
        map2 %* written1 ->
        FoldConst (s1;;s2) map_in (t1;;t2) map2' (written1 + written2).

Hint Constructors FoldConst.

Ltac descend :=
  repeat match goal with
           | [ |- exists x, _ ] => eexists
         end.

Lemma FoldConst_Seq_elim : 
  forall s map_in t map_out written, 
    FoldConst s map_in t map_out written ->
    forall s1 s2,
      s = (s1 ;; s2) ->
      exists t1 t2 written1 written2,
        t = (t1 ;; t2) /\
        written = written1 + written2 /\
        ((exists map,
            FoldConst s1 map_in t1 map written1 /\
            FoldConst s2 map t2 map_out written2) \/
         (exists map1 map1' map2,
            FoldConst s1 map1 t1 map1' written1 /\
            FoldConst s2 map2 t2 map_out written2 /\
            map1 %<= map_in /\
            map2 %<= map_in /\
            map2 %* written1)).
Proof.
  induction 1; simpl; intuition; unfold_all; subst.
  simpl; descend; intuition; left; descend; intuition.
  edestruct IHFoldConst; eauto; openhyp; subst.
  descend; intuition eauto.
  descend; repeat split.
  right; descend.
  repeat split.
  5 : eauto.
  eauto.
  eauto.
  eauto using submap_trans.
  eauto using submap_trans.
  injection H1; intros; subst; descend; intuition eauto.
  injection H4; intros; subst; descend; intuition eauto; right; descend; intuition eauto.
Qed.

Inductive NotSeq : Statement -> Prop :=
  | IsSkip : NotSeq skip
  | IsIf : forall c t f, NotSeq (If c {t} else {f})
  | IsWhile : forall c b, NotSeq (While (c) {{b}})
  | IsAssign : forall x e, NotSeq (x <- e)
  | IsRead : forall x arr idx, NotSeq (x <== arr[idx])
  | IsWrite : forall arr idx e, NotSeq (arr[idx] <== e)
  | IsMalloc : forall x size, NotSeq (x <- new size)
  | IsFree : forall arr, NotSeq (delete arr)
  | IsLen : forall x arr, NotSeq (Syntax.Len x arr)
  | IsCall : forall f x, NotSeq (Syntax.Call f x)
.

Hint Constructors NotSeq.

Lemma FoldConst_NotSeq_elim : 
  forall s map_in t map_out written, 
    FoldConst s map_in t map_out written -> 
    NotSeq s ->
    exists map_in', 
      let result := const_folding s map_in' in
      let s' := fst (fst result) in
      let map_out' := snd (fst result) in
      let written' := snd result in
      t = s' /\
      map_in' %<= map_in /\ 
      map_out %<= map_out' /\
      written = written'.
Proof.
  induction 1; simpl; intuition; unfold_all; subst.
  inversion H; subst; simpl; descend; eauto.
  openhyp; subst; descend; intuition eauto using submap_trans.
  inversion H1.
  inversion H4.
Qed.

Definition const_folding_rel vs s vt t := 
  exists map map' written,
    FoldConst s map t map' written /\
    vt = vs /\
    agree_with vs map.

Hint Unfold const_folding_rel.

Lemma FoldConst_skip : forall map map', map' %<= map -> FoldConst skip map skip map' {}.
  intros.
  econstructor 2.
  econstructor 1.
  eauto.
  simpl.
  eauto.
Qed.
Hint Resolve FoldConst_skip.

Ltac filter_case :=
  match goal with
    | H : context [Syntax.Assignment] |- _ => fail 1
    | H : context [Syntax.Seq] |- _ => fail 1
    | H : context [Syntax.Conditional] |- _ => fail 1
    | H : context [Syntax.Loop] |- _ => fail 1
    | |- _ => idtac
  end.

Ltac openhyp' :=
  repeat match goal with
           | H : context [const_dec ?E] |- _ => destruct (const_dec E)
           | H : context [const_zero_dec ?E] |- _ => destruct (const_zero_dec E)
           | H : context [ { _ | _ } ] |- _ => destruct H
         end.

Lemma everything_agree_with_empty_map : forall v, agree_with v empty_map.
  admit.
Qed.
Hint Resolve everything_agree_with_empty_map.

Lemma empty_map_submap : forall m, empty_map %<= m.
  admit.
Qed.
Hint Resolve empty_map_submap.

Lemma not_const_zero_empty_map : forall e m, const_folding_expr e m <> Const $0 -> const_folding_expr e empty_map <> Const $0.
  admit.
Qed.
Hint Resolve not_const_zero_empty_map.

Lemma not_const_zero_submap : forall e m m', const_folding_expr e m <> Const $0 -> m' %<= m -> const_folding_expr e m' <> Const $0.
  admit.
Qed.
Hint Resolve not_const_zero_submap.

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

Lemma agree_with_agree_except_disjoint : forall local1 local2 m s, agree_with local1 m -> m %* s -> agree_except local1 local2 s -> agree_with local2 m.
  admit.
Qed.
Hint Resolve agree_with_agree_except_disjoint.

Lemma agree_with_agree_except_subtract : forall v1 v2 m s, agree_with v1 m -> agree_except v1 v2 s -> agree_with v2 (m - s).
  admit.
Qed.
Hint Resolve agree_with_agree_except_subtract.

Lemma out_map_upper_bound : forall s map_in t map_out written, FoldConst s map_in t map_out written -> map_out - written %<= map_in.
  admit.
Qed.
Hint Resolve out_map_upper_bound.

Variable subset : SET -> SET -> Prop.

Infix "%%<=" := subset (at level 60).

Lemma subset_union_left : forall a b c, a %%<= b -> a %%<= c + b.
  admit.
Qed.
Hint Resolve subset_union_left.

Lemma subset_union_right_both : forall a b c, a %%<= b -> a + c %%<= b + c.
  admit.
Qed.
Hint Resolve subset_union_right_both.

Variable upds : PartialMap -> PartialMap -> PartialMap.

Variable compatible : PartialMap -> PartialMap -> Prop.

Lemma agree_except_incl : forall v1 v2 s s', agree_except v1 v2 s -> s %%<= s' -> agree_except v1 v2 s'.
  admit.
Qed.
Hint Resolve agree_except_incl.

Lemma subset_union_2 : forall a b, a %%<= a + b.
  admit.
Qed.
Hint Resolve subset_union_2.

Lemma compatible_upds_enlarge1 : forall v1 v2, compatible v1 v2 -> v1 %<= upds v1 v2.
  admit.
Qed.
Hint Resolve compatible_upds_enlarge1.

Lemma compatible_upds_enlarge2 : forall v1 v2, compatible v1 v2 -> v2 %<= upds v1 v2.
  admit.
Qed.
Hint Resolve compatible_upds_enlarge2.

Lemma disjoint_upds_compatible : forall v1 v2 s, compatible (v1 - s) v2 -> v2 %* s -> compatible v1 v2.
  admit.
Qed.
Hint Resolve disjoint_upds_compatible.

Lemma both_submap_compatible : forall v1 v2 v3, v1 %<= v3 -> v2 %<= v3 -> compatible v1 v2.
  admit.
Qed.
Hint Resolve both_submap_compatible.

Lemma subset_disjoint : forall m s s', m %* s -> s' %%<= s -> m %* s'.
  admit.
Qed.
Hint Resolve subset_disjoint.

Lemma compatible_agree_with_both : forall v m1 m2, agree_with v m1 -> agree_with v m2 -> compatible m1 m2 -> agree_with v (upds m1 m2).
  admit.
Qed.
Hint Resolve compatible_agree_with_both.

Lemma upds_subtract_1 : forall m1 m2 s, upds m1 m2 - s %<= upds (m1 - s) m2.
  admit.
Qed.

Lemma both_submap_upds_submap : forall m1 m2 m, m1 %<= m -> m2 %<= m -> upds m1 m2 %<= m.
  admit.
Qed.
Hint Resolve both_submap_upds_submap.

Lemma subset_union_1 : forall a b, a %%<= b + a.
  admit.
Qed.
Hint Resolve subset_union_1.

Lemma subset_union_right : forall a b c, a %%<= b -> a %%<= b + c.
  admit.
Qed.
Hint Resolve subset_union_right.

Lemma subset_refl : forall s, s %%<= s.
  admit.
Qed.
Hint Resolve subset_refl.

Lemma submap_subtract_twice : forall a b, a - b %<= a - b - b.
  admit.
Qed.
Hint Resolve submap_subtract_twice.

Lemma union_same_subset : forall s, s + s %%<= s.
  admit.
Qed.
Hint Resolve union_same_subset.

Lemma subtract_disjoint : forall m s, (m - s) %* s.
  admit.
Qed.
Hint Resolve subtract_disjoint.

Lemma subset_trans : forall a b c, a %%<= b -> b %%<= c -> a %%<= c.
  admit.
Qed.

Lemma while_case:
  forall t v v',
    Step t v v' ->
    forall s map map' written,
      FoldConst s map t map' written ->
      forall c b,
        s = Syntax.Loop c b ->
        forall vt,
          agree_with vt map ->
          forall heap,
            v = (vt, heap) ->
            (let s := b in
             (* the induction hypothesis from Lemma const_folding_is_backward_simulation' *)

             forall (t : Statement) (map map' : PartialMap) (written : SET),
               FoldConst s map t map' written ->
               forall vt : vals,
                 agree_with vt map ->
                 (forall (heap : arrays) (vt' : vals) (heap' : arrays),
                    Step t (vt, heap) (Done (vt', heap')) ->
                    Step s (vt, heap) (Done (vt', heap')) /\
                    agree_with vt' map' /\ agree_except vt vt' written) /\
                 (forall (heap : arrays) (f x : W) (t' : Statement) 
                         (vt' : vals) (heap' : arrays),
                    Step t (vt, heap) (ToCall f x t' (vt', heap')) ->
                    exists s' : Statement,
                      Step s (vt, heap) (ToCall f x s' (vt', heap')) /\
                      (exists (map_k map_k' : PartialMap) (written_k : SET),
                         FoldConst s' map_k t' map_k' written_k /\
                         agree_with vt' map_k /\
                         agree_except vt vt' written /\
                         map_k - written %<= map /\
                         map' %<= map_k' /\ 
                         written_k %%<= written))

            ) ->
            (forall vt' heap',
               v' = Done (vt', heap') ->
               Step s (vt, heap) (Done (vt', heap')) /\
               agree_with vt' map' /\ 
               agree_except vt vt' written) /\
            (forall f x t' vt' heap',
               v' = ToCall f x t' (vt', heap') ->
               exists s',
                 Step s (vt, heap) (ToCall f x s' (vt', heap')) /\
                 exists map_k map_k' written_k,
                   FoldConst s' map_k t' map_k' written_k /\
                   agree_with vt' map_k /\
                   agree_except vt vt' written /\
                   map_k - written %<= map /\
                   map' %<= map_k' /\ 
                   written_k %%<= written).
Proof.
  induction 1; simpl; intros; unfold_all; subst.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.

  split; intros; subst.

  eapply FoldConst_NotSeq_elim in H2; simpl in *; eauto; openhyp; subst; destruct (const_zero_dec _); simpl in *.

  intuition.
  
  injection H2; intros; subst.
  destruct v'; simpl in *.
  eapply H6 in H0; eauto; openhyp.
  repeat erewrite const_folding_expr_correct in * by eauto.
  edestruct IHStep2; try reflexivity.
  3 : eauto.
  replace (While (const_folding_expr c _) {{fst (fst (const_folding b _))}}) with (fst (fst (const_folding (While (c) {{b}} ) (x - snd (const_folding b []))))) by (simpl in *; destruct (const_zero_dec _); [contradict e; eauto | simpl; eauto ]).
  eauto.
  eauto.
  edestruct H9; eauto; openhyp.
  simpl in *; openhyp'; [ contradict e; eauto | ].
  simpl in *.
  intuition eauto using submap_trans.

  eapply FoldConst_NotSeq_elim in H2; simpl in *; eauto; openhyp; subst; destruct (const_zero_dec _); simpl in *.

  intuition.
  
  injection H2; intros; subst.
  destruct v'; simpl in *.
  eapply H6 in H0; eauto; openhyp.
  repeat erewrite const_folding_expr_correct in * by eauto.
  edestruct IHStep2; try reflexivity.
  3 : eauto.
  replace (While (const_folding_expr c _) {{fst (fst (const_folding b _))}}) with (fst (fst (const_folding (While (c) {{b}} ) (x0 - snd (const_folding b []))))) by (simpl in *; destruct (const_zero_dec _); [contradict e; eauto | simpl; eauto ]).
  eauto.
  eauto.
  edestruct H10; eauto; openhyp.
  simpl in *; openhyp'; [ contradict e; eauto | ].
  simpl in *.
  descend; intuition eauto; descend; intuition eauto using submap_trans.

  split; intros; subst.

  intuition.

  eapply FoldConst_NotSeq_elim in H1; simpl in *; eauto; openhyp; subst; destruct (const_zero_dec _); simpl in *.

  intuition.

  injection H1; intros; subst.
  injection H2; intros; subst.
  eapply H5 in H0; eauto; openhyp.
  repeat erewrite const_folding_expr_correct in * by eauto.
  descend; intuition eauto.
  descend; repeat split.
  econstructor 4.
  eauto.
  replace (While (const_folding_expr c _) {{fst (fst (const_folding b _))}}) with (fst (fst (const_folding (While (c) {{b}} ) (x1 - snd (const_folding b []))))) by (simpl in *; destruct (const_zero_dec _); [contradict e; eauto | simpl; eauto ]).
  eauto.
  eapply compatible_upds_enlarge1.
  2 : eapply compatible_upds_enlarge2.

  eauto using submap_trans.
  eauto using submap_trans.
  eauto using submap_trans.

  eapply compatible_agree_with_both.
  eauto.
  2 : eauto using submap_trans.
  eapply agree_with_agree_except_disjoint.
  eauto using submap_trans.
  eauto.
  eauto.
  eauto.
  eapply submap_trans.
  eapply upds_subtract_1.
  eauto using submap_trans.
  simpl in *; destruct (const_zero_dec _); [contradict e; eauto | simpl; eauto ].
  eauto using submap_trans.
  simpl in *; destruct (const_zero_dec _); [contradict e; eauto | simpl; eauto ].

  eauto using subset_trans.

  eapply FoldConst_NotSeq_elim in H; simpl in *; eauto; openhyp; subst; openhyp'; simpl in *; intuition.

  eapply FoldConst_NotSeq_elim in H0; simpl in *; eauto; openhyp; subst; openhyp'; simpl in *; intuition.

  eapply FoldConst_NotSeq_elim in H0; simpl in *; eauto; openhyp; subst; openhyp'; simpl in *; intuition.

  eapply FoldConst_NotSeq_elim in H0; simpl in *; eauto; openhyp; subst; openhyp'; simpl in *; intuition.

  eapply FoldConst_NotSeq_elim in H0; simpl in *; eauto; openhyp; subst; openhyp'; simpl in *; intuition.

  eapply FoldConst_NotSeq_elim in H2; simpl in *; eauto; openhyp; subst; openhyp'; simpl in *; intuition.
Qed.

Lemma const_folding_rel_is_backward_simulation' :
  forall s t map map' written,
    FoldConst s map t map' written ->
    forall vt,
      agree_with vt map ->
      (forall heap vt' heap',
         Step t (vt, heap) (Done (vt', heap')) ->
         Step s (vt, heap) (Done (vt', heap')) /\
         agree_with vt' map' /\ 
         agree_except vt vt' written) /\
      (forall heap f x t' vt' heap',
         Step t (vt, heap) (ToCall f x t' (vt', heap')) ->
         exists s',
           Step s (vt, heap) (ToCall f x s' (vt', heap')) /\
           exists map_k map_k' written_k,
             FoldConst s' map_k t' map_k' written_k /\
             agree_with vt' map_k /\
             agree_except vt vt' written /\
             map_k - written %<= map /\
             map' %<= map_k' /\ 
             written_k %%<= written).
Proof.
  induction s; try solve [simpl; intuition]; intros; try solve [ filter_case; split; intros; eapply FoldConst_NotSeq_elim in H; simpl in *; eauto; openhyp; subst; inversion H1; unfold_all; subst; subst; repeat erewrite const_folding_expr_correct in * by eauto; descend; intuition; descend; intuition eauto using submap_trans ].

  Focus 4.

  (* while *)
  intros; split; intros; eapply while_case in H; eauto; openhyp; eauto.

  (* assign *)
  split; intros; eapply FoldConst_NotSeq_elim in H; simpl in *; eauto; openhyp; subst; openhyp'; simpl in *; inversion H1; unfold_all; subst; [ rewrite <- e0 | ]; repeat erewrite const_folding_expr_correct in * by eauto; intuition eauto.
  erewrite <- const_folding_expr_correct'.
  2 : symmetry; eauto.
  2 : eauto.
  simpl; eauto.

  (* seq *)
  split; intros; eapply FoldConst_Seq_elim in H; eauto; openhyp; subst; inversion H1; subst.
  destruct v'; simpl in *; eapply IHs1 in H5; eauto; openhyp; eapply IHs2 in H8; eauto; openhyp; descend; intuition eauto; descend; intuition eauto.
  destruct v'; simpl in *; eapply IHs1 in H8; eauto; openhyp; eapply IHs2 in H11; eauto; openhyp; descend; intuition eauto; descend; intuition eauto using submap_trans.
  destruct v'; simpl in *; eapply IHs1 in H5; eauto; openhyp; eapply IHs2 in H8; eauto; openhyp; descend; intuition eauto; descend; intuition eauto using submap_trans.
  eapply IHs1 in H6; eauto; openhyp; descend; intuition eauto; eexists; exists map'; descend; intuition eauto using submap_trans.  
  destruct v'; simpl in *; eapply IHs1 in H8; eauto; openhyp; eapply IHs2 in H11; eauto; openhyp; descend; intuition eauto; descend; intuition eauto using submap_trans.
  eapply IHs1 in H9; eauto; openhyp; descend; intuition eauto.
  descend; repeat split.
  econstructor 4.
  eauto.
  eauto.
  eapply compatible_upds_enlarge1.
  2 : eapply compatible_upds_enlarge2.

  eauto using submap_trans.
  eauto using submap_trans.
  
  eauto.

  eapply compatible_agree_with_both.
  eauto.
  2 : eauto using submap_trans.
  eapply agree_with_agree_except_disjoint.
  eauto using submap_trans.
  eauto.
  eauto.
  eauto.
  eapply submap_trans.
  eapply subtract_union_submap.
  eapply submap_trans.
  eapply subtract_submap.
  eapply submap_trans.
  eapply upds_subtract_1.
  eauto using submap_trans.
  eauto.
  eauto.

  (* if *)
  split.

  intros; eapply FoldConst_NotSeq_elim in H; simpl in *; eauto; openhyp; subst; destruct (const_dec _).

  destruct s; destruct (Sumbool.sumbool_of_bool (wneb x0 $0)); erewrite e1 in *; [ eapply IHs1 in H1 | eapply IHs2 in H1 ]; eauto; openhyp; replace x0 with (exprDenote x0 vt) in e1 by eauto; rewrite <- e0 in e1; repeat erewrite const_folding_expr_correct in * by eauto; intuition eauto.

  simpl in *; inversion H1; subst; repeat erewrite const_folding_expr_correct in * by eauto; simpl in *; [ eapply IHs1 in H9 | eapply IHs2 in H9 ]; eauto; openhyp; subst; descend; intuition eauto.

  intros; eapply FoldConst_NotSeq_elim in H; simpl in *; eauto; openhyp; subst; destruct (const_dec _).

  destruct s; destruct (Sumbool.sumbool_of_bool (wneb x1 $0)); erewrite e1 in *; [ eapply IHs1 in H1 | eapply IHs2 in H1 ]; eauto; openhyp; replace x1 with (exprDenote x1 vt) in e1 by eauto; rewrite <- e0 in e1; repeat erewrite const_folding_expr_correct in * by eauto; descend; intuition eauto; descend; intuition eauto using submap_trans.

  simpl in *; inversion H1; subst; repeat erewrite const_folding_expr_correct in * by eauto; simpl in *; [ eapply IHs1 in H9 | eapply IHs2 in H9 ]; eauto; openhyp; subst; descend; intuition eauto; descend; intuition eauto using submap_trans.

Qed.

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
  descend; intuition eauto.
  descend; split.
  2 : eauto.
  eauto.
  intros.
  eapply H1 in H2; openhyp.
  descend; intuition eauto.
  descend; intuition eauto.
Qed.

Hint Resolve const_folding_rel_is_backward_simulation.

Definition constant_folding s := fst (fst (const_folding s empty_map)).

Lemma constant_folding_always_FoldConst : forall s map, exists map' written, FoldConst s map (constant_folding s) map' written.
  unfold constant_folding; intros; descend; intuition eauto.
Qed.

Theorem constant_folding_is_congruence : forall s v, const_folding_rel v s v (constant_folding s).
  unfold const_folding_rel; intros; exists empty_map; simpl in *; edestruct constant_folding_always_FoldConst; openhyp; descend; intuition eauto.
Qed.

Theorem constant_folding_is_backward_similar_callee : 
  forall s, is_backward_similar_callee (Internal s) (Internal (constant_folding s)).
  intros; econstructor; eauto; eapply constant_folding_is_congruence.
Qed.