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

Hypothesis sel_remove_eq : forall m x, (m %%- x) x = None.

Hypothesis sel_remove_ne : forall m x x', x <> x' -> (m %%- x) x' = m x'.

Hypothesis sel_add_eq : forall m x w, (m %%+ (x, w)) x = Some w.

Hypothesis sel_add_ne : forall m x w x', x <> x' -> (m %%+ (x, w)) x' = m x'.

Definition const_dec : forall e, {w | e = Const w} + {~ exists w, e = Const w}.
  intros; destruct e; solve[ right; intuition; openhyp; intuition | left; eauto ].
Qed.

Inductive IsConstZero := 
  | IsConstZeroYes : IsConstZero
  | IsConstZeroNo : Expr -> IsConstZero.

Definition is_zero e : IsConstZero :=
  match e with
    | Const w =>
      if wneb w $0 then
        IsConstZeroNo (Const w)
      else
        IsConstZeroYes
    | c' => IsConstZeroNo c'
  end.

Fixpoint const_folding (s : Statement) (info : Info) : Statement * Info :=
  match s with
    | Syntax.Skip => (s, info)
    | Syntax.Seq a b => 
      let (a', info') := const_folding a info in
      let (b', info'') := const_folding b info' in
      (Syntax.Seq a' b', info'')
    | Syntax.Assignment var e =>
      let e' := const_folding_expr e (fst info) in 
      let assigned_vars := snd info %+ var in
      match const_dec e' with
        | inleft (exist w _) =>
          let vars_with_known_value := fst info %%+ (var, w) in
          (Syntax.Assignment var (Const w), (vars_with_known_value, assigned_vars))
        | inright _ =>
          let vars_with_known_value := fst info %%- var in
          (Syntax.Assignment var e', (vars_with_known_value, assigned_vars))
      end
    | Conditional c t f =>
      let c' := const_folding_expr c (fst info) in 
      match const_dec c' with
        | inleft (exist w _) =>
          if wneb w $0 then
            const_folding t info
          else
            const_folding f info
        | inright _ =>
          let (t', info_t) := const_folding t (fst info, empty_Vars) in
          let (f', info_f) := const_folding f (fst info, empty_Vars) in
          (* assigned vars in branches will no longer have known values *)
          let vars_with_known_value := fst info - snd info_t - snd info_f in
          let assigned_vars := snd info + snd info_t + snd info_f in
          (Conditional c' t' f', (vars_with_known_value, assigned_vars))
      end
    | Loop c b =>
      match is_zero (const_folding_expr c (fst info)) with
        | IsConstZeroYes =>
            (Syntax.Skip, info)
        | IsConstZeroNo c' =>
          let (b', info_b) := const_folding b (fst info, empty_Vars) in
          (* assigned vars in loop body will no longer have known values *)
          let vars_with_know_value := fst info - snd info_b in
          let assigned_vars := snd info + snd info_b in
          (Loop c' b', (vars_with_know_value, assigned_vars))
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
    sel v x = w.

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

Definition sel_dec : forall (m : VarToW) x, {w | m x = Some w} + {m x = None}.
  intros; destruct (m x); intuition eauto.
Defined.

Ltac my_f_equal :=
  match goal with
    | |- (if ?E1 then _ else _) = (if ?E2 then _ else _) => replace E2 with E1; try reflexivity
  end.

Lemma const_folding_expr_correct : 
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

Lemma const_folding_expr_correct' : 
  forall e m local, 
    agree_with local m -> 
    exprDenote (const_folding_expr e m) local = exprDenote e local.
  intros; erewrite const_folding_expr_correct; eauto.
Qed.

Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Lemma assign_done : 
  forall x e info local heap local' heap', 
    let s := x <- e in
    let result := const_folding s info in
    Step (fst result) (local, heap) (Done (local', heap')) ->
    agree_with local (fst info) ->
    Step s (local, heap) (Done (local', heap')) /\
    agree_with local' (fst (snd result)).
Proof.
  intros; unfold result, s in *; clear result s; simpl in *; destruct (const_dec _); [ destruct s | ]; simpl in *; inversion H; unfold_all; subst; [ rewrite <- e0 in H | ]; erewrite const_folding_expr_correct in * by eauto; intuition.
  erewrite <- const_folding_expr_correct.
  2 : symmetry; eauto.
  2 : eauto.
  simpl; eauto.
Qed.

Hint Resolve assign_done.

Lemma break_pair : forall A B (p : A * B), p = (fst p, snd p).
  intros; destruct p; eauto.
Qed.

Variable less_informative : Info -> Info -> Prop.

Infix "%<=" := less_informative (at level 60).

Inductive FoldConst : Statement -> Info -> Statement -> Info -> Prop :=
  | OptFull : 
      forall s info, 
        FoldConst s info (fst (const_folding s info)) (snd (const_folding s info))
  | OptLess :
      forall s info_in t info_out info_in' info_out',
        FoldConst s info_in t info_out ->
        info_in %<= info_in' ->
        info_out' %<= info_out ->
        FoldConst s info_in' t info_out'
  | OptSeq : 
      forall t1 t2 s1 s2 info info' info'',
        FoldConst s1 info t1 info' ->
        FoldConst s2 info' t2 info'' ->
        FoldConst (s1;;s2) info (t1;;t2) info''.

Definition const_folding_rel vs s vt t := 
  exists info info',
    FoldConst s info t info' /\
    vt = vs /\
    agree_with vs (fst info).

Hint Unfold const_folding_rel.

Lemma less_informative_refl : forall info, info %<= info.
  admit.
Qed.
Hint Resolve less_informative_refl.

Require Import VariableLemmas.

Definition agree_except := changedVariables.

Hint Constructors FoldConst.

Ltac descend :=
  repeat match goal with
           | [ |- exists x, _ ] => eexists
         end.

Lemma less_informative_trans : forall a b c, a %<= b -> b %<= c -> a %<= c.
  admit.
Qed.

Opaque const_folding.

Lemma FoldConst_assign' : 
  forall s info_in t info_out, 
    FoldConst s info_in t info_out -> 
    forall x e,
      s = (x <- e) ->
      exists info_in' info_out', 
        (t, info_out') = const_folding (x <- e) info_in' /\ 
        info_in' %<= info_in /\ 
        info_out %<= info_out'.
Proof.
  induction 1; simpl; intuition; subst.
  descend; intuition; rewrite <- break_pair; eauto.
  edestruct IHFoldConst; eauto; openhyp; subst.
  descend; intuition eauto; eauto using less_informative_trans.
Qed.

Lemma FoldConst_assign : 
  forall x e info_in t info_out, 
    FoldConst (x <- e) info_in t info_out -> 
    exists info_in' info_out', 
      t = fst (const_folding (x <- e) info_in') /\ 
      info_out' = snd (const_folding (x <- e) info_in') /\ 
      info_in' %<= info_in /\ 
      info_out %<= info_out'.
  intros.
  eapply FoldConst_assign' in H; eauto; openhyp.
  erewrite (break_pair (const_folding _ _)) in H.
  injection H; intros; subst.
  descend; eauto.
Qed.

Variable less_informative_map : VarToW -> VarToW -> Prop.

Infix "%%<=" := less_informative_map (at level 60).

Lemma less_informative_less_informative_map : forall a b, a %<= b -> fst a %%<= fst b.
  admit.
Qed.
Hint Resolve less_informative_less_informative_map.

Lemma agree_with_less_informative_map : forall local info info', agree_with local info -> info' %%<= info -> agree_with local info'.
  admit.
Qed.
Hint Resolve agree_with_less_informative_map.

Lemma FoldConst_seq : 
  forall s1 s2 info t info', 
    FoldConst (s1;;s2) info t info' ->
    exists t1 t2 info'',
      t = (t1 ;; t2) /\
      FoldConst s1 info t1 info'' /\
      FoldConst s2 info'' t2 info'.
  admit.
Qed.

Lemma FoldConst_if : 
  forall e tt ff info_in t info_out, 
    FoldConst (If e {tt} else {ff}) info_in t info_out -> 
    exists info_in' info_out', 
      t = fst (const_folding (If e {tt} else {ff}) info_in') /\ 
      info_out' = snd (const_folding (If e {tt} else {ff}) info_in') /\ 
      info_in' %<= info_in /\ 
      info_out %<= info_out'.
  admit.
Qed.

Lemma const_folding_information_bound :
  forall s map,
    let info' := snd (const_folding s (map, empty_Vars)) in
    map - snd info' %%<= fst info'.
  admit.
Qed.

Infix "%%%<=" := List.incl (at level 60).

Lemma less_informative_map_less_informative : forall a b, fst a %%<= fst b -> snd b %%%<= snd a -> a %<= b.
  admit.
Qed.

Lemma subtract_less_information_map : forall a b, a - b %%<= a.
  admit.
Qed.

Lemma union_less_3_1 : forall a b c, b %%%<= a + b + c.
  admit.
Qed.

Lemma less_informative_map_trans : forall a b c, a %%<= b -> b %%<= c -> a %%<= c.
  admit.
Qed.

Lemma union_less_3_3 : forall a b c, c %%%<= a + b + c.
  admit.
Qed.

Lemma subtract_reorder_less : forall a b c, a - b - c %%<= a - c - b.
  admit.
Qed.

Transparent const_folding.

Lemma const_folding_rel_is_backward_simulation' :
  forall s t info info',
    FoldConst s info t info' ->
    forall vt,
      agree_with vt (fst info) ->
      (forall heap vt' heap',
         Step t (vt, heap) (Done (vt', heap')) ->
         Step s (vt, heap) (Done (vt', heap')) /\
         agree_with vt' (fst info') (* /\ *)
      (* agree_except vt vt' (snd info') *)) /\
      (forall heap f x t' vt' heap',
         Step t (vt, heap) (ToCall f x t' (vt', heap')) ->
         exists s',
           Step s (vt, heap) (ToCall f x s' (vt', heap')) /\
           exists info_k info_k',
             FoldConst s' info_k t' info_k' /\
             agree_with vt' (fst info_k) /\
             info' %<= info_k').
Proof.
  induction s; try solve [simpl; intuition]; intros.

  (* assign *)
  split.

  intros.
  eapply FoldConst_assign in H; eauto; openhyp; subst.
  eapply assign_done in H1; eauto; openhyp.
  eauto.

  intros.
  eapply FoldConst_assign in H; eauto; openhyp; subst; simpl in *; destruct (const_dec _); [ destruct s0 | ]; simpl in *; inversion H1.

  (* read *)
  split.

  intros.
  Lemma FoldConst_read : 
    forall x arr idx info_in t info_out, 
      FoldConst (x <== arr[idx]) info_in t info_out -> 
      exists info_in' info_out', 
        t = fst (const_folding (x <== arr[idx]) info_in') /\ 
        info_out' = snd (const_folding (x <==arr[idx]) info_in') /\ 
        info_in' %<= info_in /\ 
        info_out %<= info_out'.
    admit.
  Qed.
  eapply FoldConst_read in H; eauto; openhyp; subst.
  inversion H1; unfold_all; subst.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  intuition.
  simpl in *.
  eapply agree_with_less_informative_map.
  2 : eauto.
  simpl; eauto.

  intros.
  eapply FoldConst_read in H; eauto; openhyp; subst.
  simpl in *.
  inversion H1.
  
  (* write *)
  split.

  intros.
  Lemma FoldConst_write : 
    forall arr idx e info_in t info_out, 
      FoldConst (arr[idx] <== e) info_in t info_out -> 
      exists info_in' info_out', 
        t = fst (const_folding (arr[idx] <== e) info_in') /\ 
        info_out' = snd (const_folding (arr[idx] <== e) info_in') /\ 
        info_in' %<= info_in /\ 
        info_out %<= info_out'.
    admit.
  Qed.
  eapply FoldConst_write in H; eauto; openhyp; subst.
  inversion H1; unfold_all; subst.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  intuition; eauto.

  intros.
  eapply FoldConst_write in H; eauto; openhyp; subst.
  simpl in *.
  inversion H1.
  
  (* seq *)
  split.

  intros.
  eapply FoldConst_seq in H; eauto; openhyp; subst.
  inversion H1; subst.
  destruct v'; simpl in *.
  eapply IHs1 in H5; eauto; openhyp.
  eapply IHs2 in H8; eauto; openhyp.
  intuition eauto.

  intros.
  eapply FoldConst_seq in H; eauto; openhyp; subst.
  inversion H1; subst.

  destruct v'; simpl in *.
  eapply IHs1 in H5; eauto; openhyp.
  eapply IHs2 in H8; eauto; openhyp.
  eexists; intuition eauto.

  eapply IHs1 in H6; eauto; openhyp.
  eexists; intuition eauto.
  descend; intuition eauto.

  (* skip *)
  split.

  Lemma FoldConst_skip : 
    forall info_in t info_out, 
      FoldConst Syntax.Skip info_in t info_out -> 
      t = Syntax.Skip /\ 
      info_out %<= info_in.
    admit.
  Qed.

  intros; eapply FoldConst_skip in H; eauto; openhyp; subst; inversion H1; subst; eauto.

  intros; eapply FoldConst_skip in H; eauto; openhyp; subst; inversion H1; subst; eauto.

  (* if *)
  split.

  intros.
  eapply FoldConst_if in H; eauto; openhyp; subst.
  simpl in *.
  destruct (const_dec _).

  destruct s.
  destruct (Sumbool.sumbool_of_bool (wneb x0 $0)); erewrite e1 in *.
  eapply IHs1 in H1; eauto; openhyp.
  replace x0 with (exprDenote x0 vt) in e1 by eauto.
  rewrite <- e0 in e1.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  intuition eauto.
  eapply IHs2 in H1; eauto; openhyp.
  replace x0 with (exprDenote x0 vt) in e1 by eauto.
  rewrite <- e0 in e1.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  intuition eauto.

  erewrite (break_pair (const_folding s1 (fst x, empty_Vars))) in *.
  erewrite (break_pair (const_folding s2 (fst x, empty_Vars))) in *.
  simpl in *.
  inversion H1; subst.
  (* true *)
  repeat erewrite const_folding_expr_correct' in * by eauto.
  simpl in *.
  eapply IHs1 in H9; eauto; openhyp; subst.
  2 : simpl; eauto.
  descend; intuition eauto.
  eapply agree_with_less_informative_map.
  eauto.
  eapply less_informative_less_informative_map.
  eapply less_informative_trans.
  eapply H4.
  eapply less_informative_map_less_informative; simpl.
  2 : eapply union_less_3_1.
  eapply less_informative_map_trans.
  2 : eapply const_folding_information_bound.
  eapply subtract_less_information_map.
  (* false *)
  repeat erewrite const_folding_expr_correct' in * by eauto.
  simpl in *.
  eapply IHs2 in H9; eauto; openhyp; subst.
  2 : simpl; eauto.
  descend; intuition eauto.
  eapply agree_with_less_informative_map.
  eauto.
  eapply less_informative_less_informative_map.
  eapply less_informative_trans.
  eapply H4.
  eapply less_informative_map_less_informative; simpl.
  2 : eapply union_less_3_3.
  eapply less_informative_map_trans.
  eapply subtract_reorder_less.
  eapply less_informative_map_trans.
  eapply subtract_less_information_map.
  eapply const_folding_information_bound.

  intros.
  eapply FoldConst_if in H; eauto; openhyp; subst.
  simpl in *.
  destruct (const_dec _).

  destruct s.
  destruct (Sumbool.sumbool_of_bool (wneb x1 $0)); erewrite e1 in *.
  eapply IHs1 in H1; eauto; openhyp.
  replace x1 with (exprDenote x1 vt) in e1 by eauto.
  rewrite <- e0 in e1.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  descend; intuition eauto.
  descend; intuition eauto using less_informative_trans.
  eapply IHs2 in H1; eauto; openhyp.
  replace x1 with (exprDenote x1 vt) in e1 by eauto.
  rewrite <- e0 in e1.
  repeat erewrite const_folding_expr_correct' in * by eauto.
  descend; intuition eauto.
  descend; intuition eauto using less_informative_trans.

  erewrite (break_pair (const_folding s1 (fst x0, empty_Vars))) in *.
  erewrite (break_pair (const_folding s2 (fst x0, empty_Vars))) in *.
  simpl in *.
  inversion H1; subst.
  (* true *)
  repeat erewrite const_folding_expr_correct' in * by eauto.
  simpl in *.
  eapply IHs1 in H9; eauto; openhyp; subst.
  2 : simpl; eauto.
  descend; intuition eauto.
  descend; intuition eauto.
  eapply less_informative_trans.
  eapply H4.
  eapply less_informative_trans.
  Focus 2.
  eapply H6.
  eapply less_informative_map_less_informative; simpl.
  2 : eapply union_less_3_1.
  eapply less_informative_map_trans.
  2 : eapply const_folding_information_bound.
  eapply subtract_less_information_map.
  (* false *)
  repeat erewrite const_folding_expr_correct' in * by eauto.
  simpl in *.
  eapply IHs2 in H9; eauto; openhyp; subst.
  2 : simpl; eauto.
  descend; intuition eauto.
  descend; intuition eauto.
  eapply less_informative_trans.
  eapply H4.
  eapply less_informative_trans.
  Focus 2.
  eapply H6.
  eapply less_informative_map_less_informative; simpl.
  2 : eapply union_less_3_3.
  eapply less_informative_map_trans.
  eapply subtract_reorder_less.
  eapply less_informative_map_trans.
  eapply subtract_less_information_map.
  eapply const_folding_information_bound.

  admit.
  admit.
  admit.
  admit.
  admit.
Qed.

Lemma FoldConst_refl : forall s info, FoldConst (s, info) (s, info).
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

Definition empty_info := (empty_VarToW, empty_Vars).

Definition constant_folding s := fst (const_folding s empty_info).

Lemma everything_agree_with_empty_map : forall v, agree_with v empty_VarToW.
  unfold agree_with, empty_VarToW; intuition.
Qed.
Hint Resolve everything_agree_with_empty_map.

Lemma constant_folding_always_FoldConst : forall s info, exists info', FoldConst (s, info) (constant_folding s, info').
  admit.
Qed.

Theorem constant_folding_is_congruence : forall s v, const_folding_rel v s v (constant_folding s).
  unfold const_folding_rel; intros; exists empty_info; simpl in *; edestruct constant_folding_always_FoldConst; intuition eauto.
Qed.

Theorem constant_folding_is_backward_similar_callee : 
  forall s, is_backward_similar_callee (Internal s) (Internal (constant_folding s)).
  intros; econstructor; eauto; eapply constant_folding_is_congruence.
Qed.