Require Import Equalities.

Set Implicit Arguments.

Module Type Set_ (Key : MiniDecidableType).

  Delimit Scope set_scope with set.

  Local Open Scope set_scope.

  Parameter set : Type.

  Parameter mem : Key.t -> set -> Prop.
  Infix "%in" := mem (at level 60): set_scope.

  Parameter union : set -> set -> set.
  Infix "+" := union : set_scope.

  Parameter empty : set.
  Notation "{}" := empty : set_scope.

  Parameter singleton : Key.t -> set.
  Notation "{ x }" := (singleton x) : set_scope.

  Parameter singleton_mem : forall x, mem x {x}.

  Parameter subset : set -> set -> Prop.
  Infix "<=" := subset : set_scope.

  Parameter subset_correct : forall a b, a <= b -> forall x, x %in a -> x %in b.

  Parameter subset_refl : forall s, s <= s.

  Parameter subset_union_2 : forall a b, a <= a + b.

  Parameter subset_union_1 : forall a b, a <= b + a.

  Parameter union_same_subset : forall s, s + s <= s.

End Set_.

Module Type MembershipDecidableSet (Key : MiniDecidableType) <: Set_ Key.
  
  Include Set_ Key.

  Parameter mem_dec : forall x s, {mem x s} + {~ mem x s}.

End MembershipDecidableSet.

(* Implementations *)

Module ArrowSet (Key : MiniDecidableType) : MembershipDecidableSet Key.

  Definition set := Key.t -> bool.

  Definition mem x (s : set) := s x = true.

  Definition union (a b : set) := fun x => orb (a x) (b x).

  Definition empty : set := fun _ => false.

  Definition singleton a : set := fun x => if Key.eq_dec x a then true else false.

  Lemma singleton_mem : forall x, mem x (singleton x).
    unfold singleton, mem; intros; destruct (Key.eq_dec x x); eauto.
  Qed.

  Definition subset (a b : set) := forall x, mem x a -> mem x b.

  Lemma subset_correct : forall a b, subset a b -> forall x, mem x a -> mem x b.
    eauto.
  Qed.

  Definition subset_refl : forall s, subset s s.
    unfold subset; intuition.
  Qed.

  Definition subset_union_2 : forall a b, subset a (union a b).
    unfold subset, union, mem; intuition.
  Qed.
  
  Definition subset_union_1 : forall a b, subset a (union b a).
    unfold subset, union, mem; intuition.
  Qed.

  Definition union_same_subset : forall s, subset (union s s) s.
    unfold subset, union, mem; intuition.
    eapply Bool.orb_true_elim in H.
    destruct H; eauto.
  Qed.

  Definition mem_dec : forall x s, {mem x s} + {~ mem x s}.
    unfold mem; intros; destruct (Bool.bool_dec (s x) true); intuition.
  Qed.

End ArrowSet.

