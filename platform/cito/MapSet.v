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

Lemma empty_map_empty : forall x, sel [] x = None.
  admit.
Qed.

Definition submap (a b : PartialMap) := forall x w, sel a x = Some w -> sel b x = Some w.

Infix "%%<=" := submap (at level 60) : mapset_scope.

Lemma submap_correct : forall a b, a %%<= b -> forall x w, sel a x = Some w -> sel b x = Some w.
  admit.
Qed.

Lemma empty_map_submap : forall m, empty_map %%<= m.
  admit.
Qed.

(* SET *)

Variable SET : Set.

Variable mem : string -> SET -> Prop.
Infix "%in" := mem (at level 60): mapset_scope.

Variable union : SET -> SET -> SET.
Infix "+" := union : mapset_scope.

Variable empty_set : SET.

Notation "{}" := empty_set : mapset_scope.

Variable singleton_set : string -> SET.

Notation "{ x }" := (singleton_set x) : mapset_scope.

Lemma singleton_mem : forall x, x %in singleton_set x.
  admit.
Qed.

Variable subset : SET -> SET -> Prop.

Infix "%<=" := subset (at level 60) : mapset_scope.

Lemma subset_correct : forall a b, a %<= b -> forall x, x %in a -> x %in b.
  admit.
Qed.

Lemma subset_union_2 : forall a b, a %<= a + b.
  admit.
Qed.

Lemma subset_union_1 : forall a b, a %<= b + a.
  admit.
Qed.

Lemma subset_refl : forall s, s %<= s.
  admit.
Qed.

Lemma union_same_subset : forall s, s + s %<= s.
  admit.
Qed.

(* subtract *)

Variable subtract : PartialMap -> SET -> PartialMap.
Infix "-" := subtract : mapset_scope.

Lemma subtract_submap : forall a b, a - b %%<= a.
  admit.
Qed.

Lemma subtract_none : forall m s x, x %in s -> sel (m - s) x = None.
  admit.
Qed.