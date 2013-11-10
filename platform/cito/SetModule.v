Require Import Equalities.

Set Implicit Arguments.

Module Type Set_ (Key : MiniDecidableType).

  Parameter set : Type.

  Parameter mem : Key.t -> set -> Prop.

  Parameter union : set -> set -> set.

  Parameter union_has_left : forall a b x, mem x a -> mem x (union a b).

  Parameter union_has_right : forall a b x, mem x b -> mem x (union a b).

  Parameter union_elim : forall a b x, mem x (union a b) -> mem x a \/ mem x b.

  Parameter empty : set.

  Parameter empty_correct : forall x, ~ mem x empty.

  Parameter add : set -> Key.t -> set.

  Parameter add_added : forall s x, mem x (add s x).

End Set_.

Module Type MembershipDecidableSet (Key : MiniDecidableType) <: Set_ Key.
  
  Include Set_ Key.

  Parameter mem_dec : forall x s, {mem x s} + {~ mem x s}.

End MembershipDecidableSet.

Module Notations (Key : MiniDecidableType) (Import S : Set_ Key).
  Delimit Scope set_scope with set.
  Infix "%in" := mem (at level 60): set_scope.
  Infix "+" := union : set_scope.
  Notation "{}" := empty : set_scope.
End Notations.

Module Relations (Key : MiniDecidableType) (Import S : Set_ Key).

  Definition subset (a b : set) := forall x, mem x a -> mem x b.
  Infix "<=" := subset : set_scope.

  Lemma subset_correct : forall a b, subset a b -> forall x, mem x a -> mem x b.
    eauto.
  Qed.

  Definition subset_refl : forall s, subset s s.
    unfold subset; intuition.
  Qed.

  Definition subset_union_2 : forall a b, subset a (union a b).
    unfold subset; intros; eapply union_has_left; eauto.
  Qed.
  
  Definition subset_union_1 : forall a b, subset a (union b a).
    unfold subset; intros; eapply union_has_right; eauto.
  Qed.

  Definition union_same_subset : forall s, subset (union s s) s.
    unfold subset; intros; eapply union_elim in H; destruct H; eauto.
  Qed.

End Relations.

Module Singleton (Key : MiniDecidableType) (Import S : Set_ Key).

  Definition singleton x := add empty x.
  Notation "{ x }" := (singleton x) : set_scope.

  Lemma singleton_mem : forall x, mem x (singleton x).
    unfold singleton; intros; eapply add_added.
  Qed.

End Singleton.

(* Implementations *)

Module ArrowSet (Key : MiniDecidableType) <: MembershipDecidableSet Key.

  Definition set := Key.t -> bool.

  Definition mem x (s : set) := s x = true.

  Definition union (a b : set) := fun x => orb (a x) (b x).

  Lemma union_has_left : forall a b x, mem x a -> mem x (union a b).
    unfold mem, union; intuition.
  Qed.

  Lemma union_has_right : forall a b x, mem x b -> mem x (union a b).
    unfold mem, union; intuition.
  Qed.

  Lemma union_elim : forall a b x, mem x (union a b) -> mem x a \/ mem x b.
    unfold mem, union.
    intros.
    eapply Bool.orb_true_elim in H.
    destruct H; intuition.
  Qed.
  
  Definition empty : set := fun _ => false.

  Lemma empty_correct : forall x, ~ mem x empty.
    unfold empty, mem; eauto.
  Qed.

  Definition add (s : set) x : set :=
    fun x' =>
      if Key.eq_dec x' x then
        true
      else
        s x'.

  Lemma add_added : forall s x, mem x (add s x).
    unfold add, mem; intros; destruct (Key.eq_dec x x); eauto.
  Qed.

  Definition mem_dec : forall x s, {mem x s} + {~ mem x s}.
    unfold mem; intros; destruct (Bool.bool_dec (s x) true); intuition.
  Qed.

  Include Notations Key.
  Include Relations Key.
  Include Singleton Key.

End ArrowSet.

