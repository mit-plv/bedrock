Require Import OrderedType. 

Module Ordered_nat <: OrderedType with Definition t := nat.
  Definition t := nat.
  Definition eq := @eq nat. 
  Definition lt := @lt.

  About OrderedType.OrderedType.

  Theorem eq_refl : forall x, eq x x.
    reflexivity.
  Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
    intros; symmetry; auto.
  Qed.    

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
    intros; etransitivity; eauto.
  Qed.

  Require Import Omega.
  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
    intros. unfold lt in *. omega.
  Qed.
     
  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
    unfold eq, lt. intros; omega.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match Compare_dec.lt_eq_lt_dec x y with 
      | inleft (left pf) => OrderedType.LT _ pf
      | inleft (right pf) => OrderedType.EQ _ pf
      | inright pf => OrderedType.GT _ pf
    end.

  Definition eq_dec : forall x y : nat, {x = y} + {x <> y} := 
    Peano_dec.eq_nat_dec.

End Ordered_nat.

Require Bedrock.FMapAVL.

Require ZArith.Int.

Module IntMap := Bedrock.FMapAVL.Raw ZArith.Int.Z_as_Int Ordered_nat.
