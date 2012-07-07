Require Import AutoSep Malloc.


(** * Bags -- move to a separate file eventually *)

Definition bag := W * W -> nat -> Prop.

Definition mem (p : W * W) (b : bag) := exists n, b p (S n).
Infix "%in" := mem (at level 70, no associativity).

Definition empty : bag := fun _ => eq O.

Definition equiv (b1 b2 : bag) := forall p n, b1 p n <-> b2 p n.
Infix "%=" := equiv (at level 70, no associativity).

Definition add (b : bag) (p : W * W) : bag := fun p n => exists n', n = S n' /\ b p n'.
Infix "%+" := add (at level 50, left associativity).

Definition del (b : bag) (p : W * W) : bag := fun p n => b p (S n).
Infix "%-" := del (at level 50, left associativity).

Ltac bags := subst;
  repeat match goal with
           | [ H : _ %= _ |- _ ] => generalize dependent H
           | [ H : _ %in _ |- _ ] => generalize dependent H
           | [ H : ~ _ %in _ |- _ ] => generalize dependent H
           | [ H : _ \is _ |- _ ] => generalize dependent H
         end; clear;
  unfold equiv, empty, mem, add, del, propToWord, IF_then_else; intros;
    try match goal with
          | [ |- context[?b ?p] ] =>
            match type of b with
              | bag => repeat match goal with
                                | [ H : forall x : W * W, _ |- _ ] => specialize (H p)
                              end
            end
        end; intuition; subst.

Hint Extern 5 (_ %= _) => bags.
Hint Extern 5 (_ %in _) => bags.
Hint Extern 5 (~ _ %in _) => bags.
Hint Extern 5 (_ <-> _) => bags.


Section adt.
  Variable P : bag -> W -> HProp.
  (* Abstract predicate for the data structure *)

  Variable res : nat.
  (* How many reserved stack slots? *)

  Definition initS : spec := SPEC reserving res
    PRE[_] mallocHeap
    POST[R] P empty R * mallocHeap.

  Definition isEmptyS : spec := SPEC("b") reserving res
    Ex b,
    PRE[V] P b (V "b") * mallocHeap
    POST[R] [| (b %= empty) \is R |] * P b (V "b") * mallocHeap.

  Definition enqueueS : spec := SPEC("b", "v1", "v2") reserving res
    Ex b,
    PRE[V] P b (V "b") * mallocHeap
    POST[_] P (b %+ (V "v1", V "v2")) (V "b") * mallocHeap.

  Definition dequeueS : spec := SPEC("b", "r") reserving res
    Ex b,
    PRE[V] P b (V "b") * V "r" =?> 2 * mallocHeap
    POST[_] Ex v1, Ex v2, P (b %- (v1, v2)) (V "b") * (V "r" ==*> v1, v2) * mallocHeap.
End adt.
