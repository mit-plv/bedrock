Require Import Memory String.

Set Implicit Arguments.

Delimit Scope mapset_scope with mapset.

Open Scope mapset.

(* PartialMap *)

Variable PartialMap : Set.

Variable sel : PartialMap -> string -> option W.

Variable PartialMap_add : PartialMap -> string * W -> PartialMap.
Infix "%%+" := PartialMap_add (at level 60) : mapset_scope.

Variable PartialMap_del : PartialMap -> string -> PartialMap.
Infix "%%-" := PartialMap_del (at level 60) : mapset_scope.

Hypothesis sel_remove_eq : forall m x, sel (m %%- x) x = None.

Hypothesis sel_remove_ne : forall m x x', x <> x' -> sel (m %%- x) x' = sel m x'.

Hypothesis sel_add_eq : forall m x w, sel (m %%+ (x, w)) x = Some w.

Hypothesis sel_add_ne : forall m x w x', x <> x' -> sel (m %%+ (x, w)) x' = sel m x'.

Variable empty_map : PartialMap.

Notation "[]" := empty_map : mapset_scope.

Definition submap (a b : PartialMap) := forall x w, sel a x = Some w -> sel b x = Some w.

Infix "%<=" := submap (at level 60).

Lemma empty_map_submap : forall m, empty_map %<= m.
  admit.
Qed.
Hint Resolve empty_map_submap.

(* SET *)

Variable SET : Set.

Variable union : SET -> SET -> SET.
Infix "+" := union.

Variable add : SET -> string -> SET.
Infix "%+" := add (at level 60).

Variable empty_set : SET.

Notation "{}" := empty_set : mapset_scope.

Variable singleton_set : string -> SET.

Notation "{ x }" := (singleton_set x) : mapset_scope.

Variable subset : SET -> SET -> Prop.

Infix "%%<=" := subset (at level 60).

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

(* subtract *)

Variable subtract : PartialMap -> SET -> PartialMap.
Infix "-" := subtract.

Lemma subtract_submap : forall a b, a - b %<= a.
  admit.
Qed.
Hint Resolve subtract_submap.

