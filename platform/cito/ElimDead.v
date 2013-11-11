Require Import Syntax.
Import String Memory IL SyntaxExpr.
Require Import Notations.
Require Import Equalities SetModule.
Require Import Semantics.
Require Import GeneralTactics.
Import SemanticsExpr.

Set Implicit Arguments.

Module Key <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End Key.

Module MSet := ArrowSet Key.
Import MSet.

Notation skip := Syntax.Skip.
Notation free := Syntax.Free.
Notation len := Syntax.Len.
Notation eval := exprDenote.

Open Scope stmnt.
Open Scope set.

Fixpoint used_vars e :=
  match e with
    | Const _ => 0
    | Var x => !x
    | Binop _ a b => used_vars a + used_vars b
    | TestE _ a b => used_vars a + used_vars b
  end.

Fixpoint used_vars_stmt s :=
  match s with
    | skip => 0
    | a ;;; b => used_vars_stmt a + used_vars_stmt b
    | Conditional e t f => used_vars e + used_vars_stmt t + used_vars_stmt f
    | Loop e body => used_vars e + used_vars_stmt body
    | x <- e => used_vars e
    | x <== arr[idx] => used_vars arr + used_vars idx
    | arr[idx] <== e => used_vars arr + used_vars idx + used_vars e
    | x <- new e => used_vars e
    | free e => used_vars e
    | len x e => used_vars e
    | Call f[x] => used_vars f + used_vars x
  end.

Fixpoint elim_dead s used : Statement * set :=
  match s with
    | skip => (s, used)
    | a ;;; b => 
      let result := elim_dead b used in
      let b := fst result in
      let used := snd result in
      let result := elim_dead a used in
      let a := fst result in
      let used := snd result in
      (a ;;; b, used)
    | Conditional e t f => 
      let result := elim_dead t used in
      let t := fst result in
      let used_t := snd result in
      let result := elim_dead f used in
      let f := fst result in
      let used_f := snd result in
      (Conditional e t f, used_vars e + used_t + used_f)
    | Loop e body => 
      let result := elim_dead body (used + used_vars e + used_vars_stmt body) in
      let body := fst result in
      let used' := snd result in
      (Loop e body, used + used' + used_vars e)
    | x <- e =>
      if mem_dec x used then
        (s, used - !x + used_vars e)
      else
        (skip, used)
    | x <== arr[idx] =>
      (s, used - !x + used_vars arr + used_vars idx)
    | arr[idx] <== e =>
      (s, used + used_vars arr + used_vars idx + used_vars e)
    | x <- new e =>
      (s, used - !x + used_vars e)
    | free e =>
      (s, used + used_vars e)
    | len x e =>
      (s, used - !x + used_vars e)
    | Call f[x] =>
      (s, used + used_vars f + used_vars x)
  end.

Ltac openhyp' :=
  repeat match goal with
           | H : context [mem_dec ?A ?B] |- _ => destruct (mem_dec A B)
           | |- context [mem_dec ?A ?B] => destruct (mem_dec A B)
           | H : context [ { _ | _ } ] |- _ => destruct H
         end.

Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Open Scope set_scope.

Ltac subset_solver :=
  repeat 
    match goal with
      | |- ?A <= ?A => eapply subset_refl
      | |- _ + _ <= _ => eapply union_subset
      | |- ?S <= ?A + _ =>
        match A with
            context [ S ] => eapply subset_trans; [ .. | eapply subset_union_left]
        end
      | |- ?S <= _ + ?B =>
        match B with
            context [ S ] => eapply subset_trans; [ .. | eapply subset_union_right]
        end
      | |- _ - _ <= _ => eapply subset_trans; [ eapply diff_subset | .. ]
      end.

Hint Extern 0 (subset _ _) => progress subset_solver.

Definition agree_in a b s := forall x, x ^ s -> Locals.sel a x = Locals.sel b x.

Lemma agree_in_symm : forall a b s, agree_in a b s -> agree_in b a s.
  unfold agree_in; intros; symmetry; eauto.
Qed.

Lemma agree_in_subset : forall a b s s', agree_in a b s -> (s' <= s)%set -> agree_in a b s'.
  unfold agree_in; intros; eapply subset_correct in H0; eauto.
Qed.

Lemma upd_same_agree_in : forall a b s x w, agree_in a b (s - !x) -> agree_in (upd a x w) (upd b x w) s.
  unfold agree_in; intros.
  destruct (string_dec x x0).
  subst.
  repeat rewrite sel_upd_eq; eauto.
  repeat rewrite sel_upd_ne; eauto.
  eapply H.
  eapply diff_correct.
  intuition.
  eapply singleton_correct in H1.
  intuition.
Qed.

Lemma upd_out_agree_in : forall a b s x w, agree_in a b s -> ~ x ^ s -> agree_in (upd a x w) b s.
  unfold agree_in; intros.
  destruct (string_dec x x0).
  subst; intuition.
  repeat rewrite sel_upd_ne; eauto.
Qed.

Hint Constructors RunsTo.
Hint Resolve upd_same_agree_in.
Hint Resolve agree_in_subset.
Hint Resolve upd_out_agree_in.
Hint Resolve agree_in_symm.
Hint Resolve subset_union_left subset_union_right.

Lemma elim_dead_upper_bound : 
  forall s used,
    let result := elim_dead s used in
    let used' := snd result in
    used' <= used + used_vars_stmt s.
Proof.
  induction s; simpl; intuition eauto using subset_trans.
  openhyp'; simpl in *; eauto.
Qed.
Hint Resolve elim_dead_upper_bound.

Ltac f_equal' :=
  match goal with
    | |- (if ?E1 then _ else _) = (if ?E2 then _ else _) => replace E2 with E1; try reflexivity
  end.

Lemma eval_agree_in : forall e a b, agree_in a b (used_vars e) -> eval e a = eval e b.
  induction e; simpl; intuition.
  eapply H; eapply singleton_correct; eauto.
  f_equal; eauto.
  f_equal'; f_equal; eauto.
Qed.

Lemma while_case :
  forall fs t v v',
    RunsTo fs t v v' ->
    forall e body used vs,
      let s := Loop e body in
      let result := elim_dead s used in
      let s' := fst result in
      let used' := snd result in
      let vt := fst v in
      let heap := snd v in
      let vt' := fst v' in
      let heap' := snd v' in
      t = s' ->
      agree_in vs vt used' ->
      (
        let s := body in

        forall (used : set) (vs vt : vals) (heap : arrays) 
               (vt' : vals) (heap' : arrays),
          let result := elim_dead s used in
          let t := fst result in
          let used' := snd result in
          RunsTo fs t (vt, heap) (vt', heap') ->
          agree_in vs vt used' ->
          exists vs' : vals,
            RunsTo fs s (vs, heap) (vs', heap') /\ agree_in vs' vt' used
      ) ->
      exists vs',
        RunsTo fs s (vs, heap) (vs', heap') /\
        agree_in vs' vt' used.
Proof.
  induction 1; simpl; intros; unfold_all; subst; intuition.

  injection H2; intros; subst.
  destruct v; simpl in *.
  destruct v'; simpl in *.
  eapply H4 in H0; eauto; openhyp.
  destruct v''; simpl in *.
  edestruct IHRunsTo2; try reflexivity.
  2 : eauto.
  eauto using subset_trans.
  openhyp.
  descend.
  econstructor.
  simpl. 
  repeat erewrite (@eval_agree_in _ vs w) by eauto.
  eauto.
  eauto.
  eauto.
  eauto.

  injection H0; intros; subst.
  descend.
  econstructor 9.
  simpl.
  repeat erewrite (@eval_agree_in _ vs (fst v)) by eauto.
  eauto.
  eauto.
Qed.

Lemma elim_dead_is_bp : 
  forall fs s used vs vt heap vt' heap', 
    let result := elim_dead s used in
    let t := fst result in
    let used' := snd result in
    RunsTo fs t (vt, heap) (vt', heap') ->
    agree_in vs vt used' ->
    exists vs',
      RunsTo fs s (vs, heap) (vs', heap') /\
      agree_in vs' vt' used.
Proof.
  induction s; simpl; intros.

  openhyp'; simpl in *.
  inversion H; unfold_all; subst.
  descend; intuition.
  erewrite eval_agree_in by eauto.
  eauto.

  inversion H; unfold_all; subst.
  descend; intuition.

  inversion H; unfold_all; subst.
  descend.
  econstructor.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.

  inversion H; unfold_all; subst.
  descend; intuition.
  repeat erewrite (@eval_agree_in _ vt' vs) by eauto.
  econstructor.
  repeat erewrite (@eval_agree_in _ vs vt') by eauto.
  eauto.
  eauto.
  
  inversion H; unfold_all; subst.
  destruct v'; simpl in *.
  eapply IHs1 in H3; eauto; openhyp.
  eapply IHs2 in H6; eauto; openhyp.
  descend.
  eauto.
  eauto.

  inversion H; unfold_all; subst.
  descend.
  eauto.
  eauto.

  inversion H; unfold_all; subst.
  simpl in *.
  eapply IHs1 in H7; eauto; openhyp.
  descend.
  econstructor.
  simpl.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.
  eauto.
  eauto.

  simpl in *.
  eapply IHs2 in H7; eauto; openhyp.
  descend.
  econstructor 7.
  simpl.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.
  eauto.
  eauto.

  eapply while_case in H; eauto.

  inversion H; unfold_all; subst.
  descend.
  econstructor.
  eauto.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.
  eauto.

  inversion H; unfold_all; subst.
  descend.
  repeat erewrite (@eval_agree_in _ vt' vs) by eauto.
  econstructor.
  repeat erewrite (@eval_agree_in _ vs vt') by eauto.
  eauto.
  eauto.

  inversion H; unfold_all; subst.
  descend.
  econstructor.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.
  repeat erewrite (@eval_agree_in _ vs vt) by eauto.
  eauto.

  inversion H; unfold_all; subst.
  descend.
  econstructor.
  repeat erewrite (@eval_agree_in _ vs vt') by eauto.
  eauto.
  repeat erewrite (@eval_agree_in _ vs vt') by eauto.
  eauto.
  eauto.

  descend.
  econstructor 14.
  repeat erewrite (@eval_agree_in _ vs vt') by eauto.
  eauto.
  repeat erewrite (@eval_agree_in _ vs vt') by eauto.
  eauto.
  eauto.
  eauto.

Qed.

Import Safety.

Hint Constructors Safe.

Lemma elim_dead_is_sp :
  forall fs s used vs vt heap,
    let result := elim_dead s used in
    let t := fst result in
    let used' := snd result in
    Safe fs s (vs, heap) ->
    agree_in vs vt used' ->
    Safe fs t (vt, heap).
Proof.
  induction s.

  Focus 7.
  intros.
  unfold_all.
  eapply 
    (Safe_coind 
       (fun t v =>
          (exists vs c b used,
             let s := While (c) {{b}} in
             let result := elim_dead s used in
             let s' := fst result in
             let used' := snd result in
             let vt := fst v in
             let heap := snd v in
             Safe fs s (vs, heap) /\
             agree_in vs vt used' /\
             (let s := b in
              forall (used : set) (vs vt : vals) (heap : arrays),
                Safe fs s (vs, heap) ->
                agree_in vs vt (snd (elim_dead s used)) ->
                Safe fs (fst (elim_dead s used)) (vt, heap)
             ) /\
             t = s') \/
          Safe fs t v
    )); [ .. | left; descend; simpl in *; intuition eauto ]; clear; simpl; intros; openhyp.

  intuition.

  inversion H; unfold_all; subst; eauto.

  intuition.

  inversion H; unfold_all; subst; eauto.

  intuition.

  inversion H; unfold_all; subst; intuition eauto.

  intuition.

  inversion H; subst.
  intuition eauto.
  right; intuition eauto.

  injection H2; intros; subst.
  inversion H; unfold_all; subst.
  destruct v; simpl in *.
  left.
  repeat split.
  repeat erewrite (@eval_agree_in _ v x) by eauto.
  eauto.
  eauto.

  intros.
  left.
  destruct v'; simpl in *.
  eapply elim_dead_is_bp in H3; eauto; openhyp.
  descend.
  4 : eauto.
  eauto.
  eauto using subset_trans.
  eauto.

  simpl in *.
  right.
  destruct v; simpl in *.
  repeat erewrite (@eval_agree_in _ v x) by eauto.
  eauto.

  inversion H; unfold_all; subst.
  intuition eauto.
  right.
  intuition eauto.

  intuition.

  inversion H; unfold_all; subst; eauto.

  intuition.

  inversion H; unfold_all; subst; eauto.

  intuition.

  inversion H; unfold_all; subst; eauto.

  intuition.

  inversion H; unfold_all; subst.
  intuition eauto.
  intuition eauto.

  (* end of while case *)

  simpl; intros; openhyp'; simpl in *; eauto.

  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.
  
  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.
  
  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  eauto.
  intros.
  destruct v'; simpl in *.
  eapply elim_dead_is_bp in H1; eauto; openhyp.
  eauto.

  simpl; intros.
  eauto.

  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  simpl in *.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.
  eauto.

  econstructor 5.
  simpl in *.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.
  eauto.

  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.
  
  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.

  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.

  simpl; intros.
  inversion H; unfold_all; subst.
  econstructor.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.

  econstructor 14.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.
  repeat erewrite (@eval_agree_in _ vt vs) by eauto.
  eauto.

Qed.  

Require Import SemanticsLemmas.
Require Import CompileStatement.

Lemma elim_dead_footprint : forall s m, List.incl (footprint (fst (elim_dead s m))) (footprint s).
Proof.
  induction s; simpl; intuition.
  openhyp'; simpl in *; eauto.
Qed.

Open Scope nat.

Lemma elim_dead_depth : forall s m, depth (fst (elim_dead s m)) <= depth s.
Proof.
  induction s; simpl; intuition.
  openhyp'; simpl in *; eauto.
Qed.

Definition elim_dead_top s := fst (elim_dead s empty).

Require Import GoodOptimizer.

Lemma same_agree_in : forall a s, agree_in a a s.
  unfold agree_in; intros; eauto.
Qed.
Hint Resolve same_agree_in.

Lemma elim_dead_top_is_good_optimizer : is_good_optimizer elim_dead_top.
  unfold is_good_optimizer, elim_dead_top.

  descend.
  destruct v; simpl in *.
  eapply elim_dead_is_bp in H; eauto; openhyp.
  descend; eauto.

  destruct v; simpl in *.
  eapply elim_dead_is_sp; eauto.

  eapply elim_dead_footprint.

  eapply elim_dead_depth.
Qed.