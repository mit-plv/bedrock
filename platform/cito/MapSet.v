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

Module Type PartialMap (Key : MiniDecidableType) (Data : Typ).

  Delimit Scope pmap_scope with pmap.

  Local Open Scope pmap_scope.

  Parameter pmap : Type.

  Parameter sel : pmap -> Key.t -> option Data.t.

  Parameter add : pmap -> Key.t * Data.t -> pmap.
  Infix "+" := add : pmap_scope.

  Parameter remove : pmap -> Key.t -> pmap.
  Infix "-" := remove : pmap_scope.

  Parameter sel_remove_eq : forall m x, sel (m - x) x = None.

  Parameter sel_remove_ne : forall m x x', x <> x' -> sel (m - x) x' = sel m x'.

  Parameter sel_add_eq : forall m x w, sel (m + (x, w)) x = Some w.

  Parameter sel_add_ne : forall m x w x', x <> x' -> sel (m + (x, w)) x' = sel m x'.

  Parameter empty : pmap.
  Notation "[]" := empty : pmap_scope.

  Parameter empty_correct : forall x, sel [] x = None.

End PartialMap.

Module Type HasSubtract (Key : MiniDecidableType) (Data : Typ) (S : Set_ Key) <: PartialMap Key Data.

  Include PartialMap Key Data.

  Local Open Scope pmap_scope.

  Parameter subtract : pmap -> S.set -> pmap.
  Infix "--" := subtract (at level 60) : pmap_scope.

  Parameter subtract_none : forall m s x, S.mem x s -> sel (m -- s) x = None.

  Parameter subtract_in : forall m s x w, sel (m -- s) x = Some w -> sel m x = Some w.

End HasSubtract.

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

Module ArrowPMap (Key : MiniDecidableType) (Data : Typ) <: PartialMap Key Data.

  Definition pmap := Key.t -> option Data.t.

  Definition sel (m : pmap) := m.

  Definition add (m : pmap) (p : Key.t * Data.t) : pmap :=
    fun k =>
      if Key.eq_dec k (fst p) then
        Some (snd p)
      else
        m k.

  Definition remove (m : pmap) (k : Key.t) : pmap :=
    fun k' =>
      if Key.eq_dec k' k then
        None
      else
        m k'.

  Lemma sel_remove_eq : forall m x, sel (remove m x) x = None.
    unfold sel, remove; intros; destruct (Key.eq_dec x x); intuition.
  Qed.
    
  Lemma sel_remove_ne : forall m x x', x <> x' -> sel (remove m x) x' = sel m x'.
    unfold sel, remove; intros; destruct (Key.eq_dec x' x); subst; intuition.
  Qed.

  Lemma sel_add_eq : forall m x w, sel (add m (x, w)) x = Some w.
    unfold sel, add; simpl; intros; destruct (Key.eq_dec x x); intuition.
  Qed.

  Lemma sel_add_ne : forall m x w x', x <> x' -> sel (add m (x, w)) x' = sel m x'.
    unfold sel, add; simpl; intros; destruct (Key.eq_dec x' x); subst; intuition.
  Qed.

  Definition empty : pmap := fun _ => None.

  Lemma empty_correct : forall x, sel empty x = None.
    eauto.
  Qed.

End ArrowPMap.

Module ArrowHasSubtract (Key : MiniDecidableType) (Data : Typ) (S : MembershipDecidableSet Key) <: HasSubtract Key Data S.

  Include ArrowPMap Key Data.

  Definition subtract (m : pmap) (s : S.set) : pmap :=
    fun k =>
      if S.mem_dec k s then
        None
      else
        sel m k.

  Lemma subtract_none : forall m s x, S.mem x s -> sel (subtract m s) x = None.
    unfold subtract, sel; intros; destruct (S.mem_dec x s); intuition.
  Qed.

  Lemma subtract_in : forall m s x w, sel (subtract m s) x = Some w -> sel m x = Some w.
    unfold subtract, sel; intros; destruct (S.mem_dec x s); intuition; discriminate.
  Qed.

End ArrowHasSubtract.

Module MakeSubmap (Key : MiniDecidableType) (Data : Typ) (M : PartialMap Key Data) <: PartialMap Key Data.

  Include M.

  Definition submap (a b : pmap) := forall x w, sel a x = Some w -> sel b x = Some w.
  Infix "<=" := submap : pmap_scope.

  Lemma submap_correct : forall a b, submap a b -> forall x w, sel a x = Some w -> sel b x = Some w.
    eauto.
  Qed.

  Lemma empty_submap : forall m, submap empty m.
    unfold submap; intros; rewrite empty_correct in H; discriminate.
  Qed.

End MakeSubmap.

Module SubtractSubmap (Key : MiniDecidableType) (Data : Typ) (S : MembershipDecidableSet Key) (M : HasSubtract Key Data S) <: HasSubtract Key Data S.

  Include M.

  Module Submap := MakeSubmap Key Data M.

  Lemma subtract_submap : forall (a : pmap) (b : S.set), Submap.submap (subtract a b) a.
    unfold Submap.submap; intros; eapply subtract_in; eauto.
  Qed.

End SubtractSubmap.