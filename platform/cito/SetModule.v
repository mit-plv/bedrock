Require Import Equalities.

Set Implicit Arguments.

Module Type Set_ (Key : MiniDecidableType).

  Parameter set : Type.

  Parameter mem : Key.t -> set -> Prop.

  Parameter union : set -> set -> set.

  Parameter union_correct : forall a b x, mem x (union a b) <-> mem x a \/ mem x b.

  Parameter diff : set -> set -> set.

  Parameter diff_correct : forall a b x, mem x (diff a b) <-> mem x a /\ ~ mem x b.

  Parameter empty : set.

  Parameter empty_correct : forall x, ~ mem x empty.

  Parameter singleton : Key.t -> set.

  Parameter singleton_correct : forall x x', mem x' (singleton x) <-> x' = x.

End Set_.

Module Type MembershipDecidableSet (Key : MiniDecidableType) <: Set_ Key.
  
  Include Set_ Key.

  Parameter mem_dec : forall x s, {mem x s} + {~ mem x s}.

End MembershipDecidableSet.

Module Notations (Key : MiniDecidableType) (Import S : Set_ Key).
  Delimit Scope set_scope with set.
  Infix "^" := mem : set_scope.
  Infix "+" := union : set_scope.
  Infix "-" := diff : set_scope.
  Notation "0" := empty : set_scope.
  Notation "!" := singleton : set_scope.
End Notations.

Module Relations (Key : MiniDecidableType) (Import S : Set_ Key).

  Definition subset (a b : set) := forall x, mem x a -> mem x b.
  Infix "<=" := subset : set_scope.

  Lemma subset_correct : forall a b, subset a b <-> forall x, mem x a -> mem x b.
    intuition.
  Qed.

  Lemma subset_refl : forall s, subset s s.
    unfold subset; intuition.
  Qed.

  Lemma subset_trans : forall a b c, subset a b -> subset b c -> subset a c.
    unfold subset; intuition.
  Qed.

  Lemma subset_union_left : forall a b, subset a (union a b).
    unfold subset; intros; eapply union_correct; eauto.
  Qed.
  
  Lemma subset_union_right : forall a b, subset b (union a b).
    unfold subset; intros; eapply union_correct; eauto.
  Qed.

  Lemma union_subset : forall (a b c : set), subset a c -> subset b c -> subset (union a b) c.
    unfold subset; intros; eapply union_correct in H1; destruct H1; eauto.
  Qed.

  Lemma union_same_subset : forall s, subset (union s s) s.
    intros; eapply union_subset; eapply subset_refl.
  Qed.

  Lemma subset_union_same : forall s, subset s (union s s).
    intros; eapply subset_union_left.
  Qed.

  Lemma diff_subset : forall a b, subset (diff a b) a.
    unfold subset; intros; eapply diff_correct in H; intuition.
  Qed.

End Relations.

Module Util (Key : MiniDecidableType) (Import S : Set_ Key).

  Lemma union_elim : forall a b x, mem x (union a b) -> mem x a \/ mem x b.
    intros; eapply union_correct in H; eauto.
  Qed.

  Lemma union_intro : forall a b x, mem x a \/ mem x b -> mem x (union a b).
    intros; eapply union_correct; eauto.
  Qed.

  Lemma mem_union_left : forall a b x, mem x a -> mem x (union a b).
    intros; eapply union_intro; intuition.
  Qed.

  Lemma mem_union_right : forall a b x, mem x b -> mem x (union a b).
    intros; eapply union_intro; intuition.
  Qed.

End Util.

(* Implementations *)

Module ArrowSet (Key : MiniDecidableType) <: MembershipDecidableSet Key.

  Definition set := Key.t -> bool.

  Definition mem x (s : set) := s x = true.

  Definition union (a b : set) := fun x => orb (a x) (b x).

  Lemma union_correct : forall a b x, mem x (union a b) <-> mem x a \/ mem x b.
    unfold mem, union; intuition; eapply Bool.orb_true_elim in H; destruct H; intuition.
  Qed.

  Definition diff (a b : set) := fun x => andb (a x) (negb (b x)).

  Lemma diff_correct : forall a b x, mem x (diff a b) <-> mem x a /\ ~ mem x b.
    unfold mem, diff; intuition; eapply Bool.andb_true_iff in H; destruct H; intuition; rewrite H0 in H1; intuition.
  Qed.

  Definition empty : set := fun _ => false.

  Lemma empty_correct : forall x, ~ mem x empty.
    unfold empty, mem; eauto.
  Qed.

  Definition singleton x := 
    fun x' =>
      if Key.eq_dec x' x then
        true
      else
        false.

  Lemma singleton_correct : forall x x', mem x' (singleton x) <-> x' = x.
    unfold mem, singleton; intros; destruct (Key.eq_dec x' x); intuition; intuition; discriminate.
  Qed.

  Definition mem_dec : forall x s, {mem x s} + {~ mem x s}.
    unfold mem; intros; destruct (Bool.bool_dec (s x) true); intuition.
  Qed.

  Include Notations Key.
  Include Relations Key.
  Include Util Key.

End ArrowSet.