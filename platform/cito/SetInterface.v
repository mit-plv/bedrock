Require Import Equalities.

Set Implicit Arguments.

Module Type Set_ (Key : MiniDecidableType).

  Parameter t : Type.

  Parameter mem : Key.t -> t -> Prop.

  Parameter union : t -> t -> t.

  Parameter union_spec : forall a b x, mem x (union a b) <-> mem x a \/ mem x b.

  Parameter diff : t -> t -> t.

  Parameter diff_spec : forall a b x, mem x (diff a b) <-> mem x a /\ ~ mem x b.

  Parameter empty : t.

  Parameter empty_spec : forall x, ~ mem x empty.

  Parameter singleton : Key.t -> t.

  Parameter singleton_spec : forall x x', mem x' (singleton x) <-> x' = x.

End Set_.

Module Type MembershipDecidableSet (Key : MiniDecidableType) <: Set_ Key.
  
  Include Set_ Key.

  Parameter mem_dec : forall x s, {mem x s} + {~ mem x s}.

End MembershipDecidableSet.