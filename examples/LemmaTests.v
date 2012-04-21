Require Import Omega.

Require Import AutoSep.


(** Let's put the lemma prover through its paces. *)

Hint Extern 1 => elimtype False; omega : contradiction.

Theorem t0 : forall a b, a =*> b ===> a =*> b.
  sepLemma.
Qed.

Theorem t1 : forall a b c d, a =*> b * c =*> d ===> c =*> d * a =*> b.
  sepLemma.
Qed.

Theorem t2 : forall P : nat -> Prop, (Ex x, [| P x |]) ===> Ex x, [| P x |].
  sepLemma; eauto.
Qed.

Theorem t3 : forall ls : list nat, [| (length ls > 0)%nat |] ===> Ex x, Ex ls', [| ls = x :: ls' |].
  destruct ls; sepLemma.  
Qed.

Theorem t4 : forall A (R : A -> A -> Prop),
  (Ex x, Ex y, Ex z, [| R x y /\ R y z |]) ===> (Ex y, ((Ex x, [| R x y |]) * (Ex z, [| R y z |]))).
  sepLemma.
  apply H.
  eassumption.
Qed.
