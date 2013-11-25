Require Import SetInterface.
Require Import SetNotations SetFunctors.
Require Import Equalities.
Require Import List.

Set Implicit Arguments.

Module Make (Key : MiniDecidableType) <: MembershipDecidableSet Key.

  Definition t := list Key.t.

  Definition mem x (s : t) := In x s.

  Definition mem_dec := in_dec Key.eq_dec.

  Definition mem_bool x s := if mem_dec x s then true else false.

  Lemma mem_bool_spec : forall s x, mem_bool x s = true <-> mem x s.
    unfold mem_bool; intros; destruct (mem_dec x s); intuition; discriminate .
  Qed.
  
  Lemma mem_bool_spec2 : forall s x, mem_bool x s = false <-> ~ mem x s.
    unfold mem_bool; intros; destruct (mem_dec x s); intuition; discriminate .
  Qed.
  
  Definition union (a b : t) := a ++ b.

  Lemma union_spec : forall a b x, mem x (union a b) <-> mem x a \/ mem x b.
    unfold mem, union; intuition.
  Qed.

  Definition diff (a b : t) := filter (fun x => negb (mem_bool x b)) a.

  Lemma negb_true : forall b, negb b = true -> b = false.
    intros; erewrite <- Bool.negb_involutive at 1; rewrite H; simpl; eauto.
  Qed.

  Lemma diff_spec : forall a b x, mem x (diff a b) <-> mem x a /\ ~ mem x b.
    unfold mem, diff; intuition.
    eapply filter_In in H.
    intuition.
    eapply filter_In in H.
    intuition.
    eapply negb_true in H2.
    eapply mem_bool_spec2 in H2.
    intuition.
    eapply filter_In.
    intuition.
    eapply mem_bool_spec2 in H1.
    rewrite H1.
    eauto.
  Qed.

  Definition empty : t := nil.

  Lemma empty_spec : forall x, ~ mem x empty.
    unfold empty, mem; eauto.
  Qed.

  Definition singleton x : t := x :: nil.

  Lemma singleton_spec : forall x x', mem x' (singleton x) <-> x' = x.
    unfold mem, In, singleton; intros; destruct (Key.eq_dec x' x); intuition; intuition.
  Qed.

  Include Notations Key.
  Include Relations Key.
  Include Util Key.

End Make.