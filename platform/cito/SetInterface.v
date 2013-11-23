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