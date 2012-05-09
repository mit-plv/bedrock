Require Import AutoSep.
Require Import List.

Set Implicit Arguments.


(** * Allocated memory regions with unknown contents *)

Fixpoint allocated (base : W) (offset len : nat) : HProp :=
  match len with
    | O => Emp
    | S len' => (Ex v, (match offset with
                          | O => base
                          | _ => base ^+ $(offset)
                        end) =*> v) * allocated base (4+offset) len'
  end%Sep.

Notation "p =?> len" := (allocated p O len) (at level 39) : Sep_scope.

Theorem allocated_extensional : forall base offset len, HProp_extensional (allocated base offset len).
  destruct len; reflexivity.
Qed.

Hint Immediate allocated_extensional.


(** * A free-list heap managed by the malloc library *)

Module Type FREE_LIST.
  Parameter freeList : nat (* number of elements in list *) -> W -> HProp.
  Parameter mallocHeap : HProp.

  Axiom freeList_extensional : forall n p, HProp_extensional (freeList n p).
  Axiom mallocHeap_extensional : HProp_extensional mallocHeap.

  Axiom mallocHeap_fwd : mallocHeap ===> Ex n, Ex p, 0 =*> p * freeList n p.
  Axiom mallocHeap_bwd : (Ex n, Ex p, 0 =*> p * freeList n p) ===> mallocHeap.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Open Scope Sep_scope.

  Fixpoint freeList (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 |]
      | S n' => [| p <> 0 |] * Ex sz, Ex p', (p ==*> $(sz), p') * (p ^+ $8) =?> sz * freeList n' p'
    end.

  Definition mallocHeap := Ex n, Ex p, 0 =*> p * freeList n p.

  Theorem freeList_extensional : forall n p, HProp_extensional (freeList n p).
    destruct n; reflexivity.
  Qed.

  Theorem mallocHeap_extensional : HProp_extensional mallocHeap.
    reflexivity.
  Qed.

  Theorem mallocHeap_fwd : mallocHeap ===> Ex n, Ex p, 0 =*> p * freeList n p.
    unfold mallocHeap; sepLemma.
  Qed.

  Theorem mallocHeap_bwd : (Ex n, Ex p, 0 =*> p * freeList n p) ===> mallocHeap.
    unfold mallocHeap; sepLemma.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.
Hint Immediate freeList_extensional mallocHeap_extensional.

Definition hints' : TacPackage.
  prepare1 mallocHeap_fwd mallocHeap_bwd.
Defined.

Definition hints : TacPackage.
  prepare2 hints'.
Defined.

Definition initS : assert := st ~> ExX, Ex n, [| st#Rv = $(n) |] /\ ![ ^[0 =?> S (S n)] * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Sp = st#Sp |] /\ ![ ^[mallocHeap] * #1 ] st').

Definition mallocM := bmodule "malloc" {{
  bfunction "init" [initS] {
    $[0] <- Rv;;
    $[4] <- 0;;
    Return 0
  }
}}.

Theorem mallocMOk : moduleOk mallocM.
  vcgen; change (natToW 0 ^+ $4) with (natToW 4) in *.
  sep hints.
  sep hints.
  instantiate (1 := 1). (** TODO: not sure if this is the right choice, needs a hint anyways **)
  admit.
Qed.
