Require Import Syntax.
Import String Memory IL SyntaxExpr.
Require Import Notations.
Require Import Equalities SetModule.

Set Implicit Arguments.

Module Key <: MiniDecidableType.
  Definition t := string.
  Definition eq_dec := string_dec.
End Key.

Module MSet := ArrowSet Key.
Import MSet.

Variable remove : set -> string -> set.
Infix "%-" := remove (at level 20).
Variable used_vars : Expr -> set.
Notation skip := Syntax.Skip.

Open Scope stmnt.
Open Scope set.

Fixpoint used_vars_stmt s :=
  match s with
    | skip => {}
    | a ;: b => used_vars_stmt a + used_vars_stmt b
    | Conditional e t f => used_vars e + used_vars_stmt t + used_vars_stmt f
    | Loop e body => used_vars e + used_vars_stmt body
    | x <- e => used_vars e
    | x <== arr[idx] => used_vars arr + used_vars idx
    | arr[idx] <== e => used_vars arr + used_vars idx + used_vars e
    | x <- new e => used_vars e
    | Free e => used_vars e
    | Len x e => used_vars e
    | Call f[x] => used_vars f + used_vars x
  end.

Fixpoint elim_dead s used : Statement * set :=
  match s with
    | skip => (s, used)
    | a ;: b => 
      let result := elim_dead b used in
      let b := fst result in
      let used := snd result in
      let result := elim_dead a used in
      let a := fst result in
      let used := snd result in
      (a ;: b, used)
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
        (s, used %- x + used_vars e)
      else
        (skip, used)
    | x <== arr[idx] =>
      (s, used %- x + used_vars arr + used_vars idx)
    | arr[idx] <== e =>
      (s, used + used_vars arr + used_vars idx + used_vars e)
    | x <- new e =>
      (s, used %- x + used_vars e)
    | Free e =>
      (s, used + used_vars e)
    | Len x e =>
      (s, used %- x + used_vars e)
    | Call f[x] =>
      (s, used + used_vars f + used_vars x)
  end.

Require Import Semantics.

Definition agree_in a b s := forall x, x %in s -> Locals.sel a x = Locals.sel b x.

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

Require Import GeneralTactics.
Import SemanticsExpr.
Notation eval := exprDenote.

Lemma eval_agree_in : forall e a b, agree_in a b (used_vars e) -> eval e a = eval e b.
  admit.
Qed.

Lemma upd_same_agree_in : forall a b s x w, agree_in a b (s %- x) -> agree_in (upd a x w) (upd b x w) s.
  admit.
Qed.

Lemma agree_in_subset : forall a b s s', agree_in a b s -> (s' <= s)%set -> agree_in a b s'.
  admit.
Qed.

Lemma upd_out_agree_in : forall a b s x w, agree_in a b s -> ~ x %in s -> agree_in (upd a x w) b s.
  admit.
Qed.

Hint Constructors RunsTo.
Hint Resolve subset_union_1 subset_union_2.

Open Scope set_scope.

Lemma union_subset : forall (a b c : set), a <= c -> b <= c -> a + b <= c.
  admit.
Qed.

Variable add : set -> string -> set.
Infix "%+" := add (at level 20).

Lemma add_subset_union : forall a x, a %+ x <= a + singleton x.
  admit.
Qed.

Lemma union_subset_add : forall a x, a + singleton x <= a %+ x.
  admit.
Qed.

Definition subset_union_left : forall a b, a <= a + b.
  admit.
Qed.

Definition subset_union_right : forall a b, b <= a + b.
  admit.
Qed.

Definition subset_trans : forall a b c, a <= b -> b <= c -> a <= c.
  admit.
Qed.

Definition remove_subset : forall a x, a %- x <= a.
  admit.
Qed.

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
      | |- _ %+ _ <= _ => eapply subset_trans; [ eapply add_subset_union | .. ]
      | |- _ <= _ %+ _ => eapply subset_trans; [ .. | eapply union_subset_add ]
      | |- _ %- _ <= _ => eapply subset_trans; [ eapply remove_subset | .. ]
      end.

Hint Extern 0 (subset _ _) => progress subset_solver.

Hint Resolve upd_same_agree_in.
Hint Resolve agree_in_subset.
Hint Resolve upd_out_agree_in.

Lemma agree_in_symm : forall a b s, agree_in a b s -> agree_in b a s.
  admit.
Qed.
Hint Resolve agree_in_symm.

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