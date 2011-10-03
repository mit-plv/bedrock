(* Make [omega] work for [N] *)

Require Import Arith Omega NArith.

Local Open Scope N_scope.

Hint Rewrite Nplus_0_r nat_of_Nsucc nat_of_Nplus N_of_nat_of_N : N.

Theorem nat_of_N_eq : forall n m,
  nat_of_N n = nat_of_N m
  -> n = m.
  intros ? ? H; apply (f_equal N_of_nat) in H;
    autorewrite with N in *; assumption.
Qed.

Theorem Nlt_out : forall n m, n < m
  -> (nat_of_N n < nat_of_N m)%nat.
  unfold Nlt; intros.
  rewrite nat_of_Ncompare in H.
  apply nat_compare_Lt_lt; assumption.
Qed.

Theorem Nlt_in : forall n m, (nat_of_N n < nat_of_N m)%nat
  -> n < m.
  unfold Nlt; intros.
  rewrite nat_of_Ncompare.
  apply (proj1 (nat_compare_lt _ _)); assumption.
Qed.

Ltac pre_nomega :=
  try (apply nat_of_N_eq || apply Nlt_in); autorewrite with N;
    repeat match goal with
             | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H
               || apply Nlt_out in H); autorewrite with N in H
           end.

Ltac nomega := pre_nomega; omega.
