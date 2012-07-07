Require Import AutoSep Malloc Bags.


(** * Queue ADT *)

Module Type QUEUE.
  Parameter queue : bag -> W -> HProp.
  Parameter lseg : bag -> nat -> W -> W -> HProp.
  Parameter lseg' : bag -> bool -> W -> W -> HProp.

  Axiom queue_extensional : forall b p, HProp_extensional (queue b p).
  Axiom lseg_extensional : forall b n fr ba, HProp_extensional (lseg b n fr ba).
  Axiom lseg'_extensional : forall b isEmpty fr ba, HProp_extensional (lseg b isEmpty fr ba).

  Axiom queue_fwd : forall b p,
    queue b p
    ===> Ex fr, Ex ba, Ex isEmpty, [| freeable p 2 |] * (p ==*> fr, ba) * lseg' b isEmpty fr ba.

  Axiom queue_bwd : forall b p,
    (Ex fr, Ex ba, Ex isEmpty, [| freeable p 2 |] * (p ==*> fr, ba) * lseg' b isEmpty fr ba)
    ===> queue b p.

  Axiom lseg'_empty_bwd : forall b isEmpty (fr : W) ba,
    fr = 0
    -> [| isEmpty = true /\ b %= empty |] ===> lseg' b isEmpty fr ba.

  Axiom lseg'_empty_fwd : forall b isEmpty (fr : W) ba,
    fr = 0
    -> lseg' b isEmpty fr ba ===> [| isEmpty = true /\ b %= empty |].

  Axiom lseg'_nonempty_fwd : forall b isEmpty (fr : W) ba,
    fr <> 0
    -> lseg' b isEmpty fr ba
    ===> [| isEmpty = false |] * Ex v1, Ex v2, Ex n, [| (v1, v2) %in b |] * lseg (b %- (v1, v2)) n fr ba * (ba ==*> v1, v2, $0).

  Axiom lseg'_nonempty_bwd : forall b isEmpty (fr : W) ba,
    fr <> 0
    -> [| isEmpty = false |] * (Ex v1, Ex v2, Ex n, [| (v1, v2) %in b |] * lseg (b %- (v1, v2)) n fr ba * (ba ==*> v1, v2, $0))
    ===> lseg' b isEmpty fr ba.
End QUEUE.

Module Queue : QUEUE.
  Open Scope Sep_scope.

  Fixpoint lseg (b : bag) (n : nat) (fr ba : W) : HProp :=
    match n with
      | O => [| fr = ba |]
      | S n' => [| fr <> ba |] * Ex v1, Ex v2, Ex p, [| (v1, v2) %in b |] * (fr ==*> v1, v2, p) * lseg (b %- (v1, v2)) n' p ba
    end.

  Definition lseg' (b : bag) (isEmpty : bool) (fr ba : W) : HProp :=
    if isEmpty
      then [| b %= empty /\ fr = 0 |]
      else [| fr <> 0 |] * Ex v1, Ex v2, Ex n, [| (v1, v2) %in b |] * lseg (b %- (v1, v2)) n fr ba * (ba ==*> v1, v2, $0).

  Definition queue (b : bag) (p : W) : HProp :=
    Ex fr, Ex ba, Ex isEmpty, [| freeable p 2 |] * (p ==*> fr, ba) * lseg' b isEmpty fr ba.

  Theorem lseg_extensional : forall b n fr ba, HProp_extensional (lseg b n fr ba).
    destruct n; reflexivity.
  Qed.

  Theorem lseg'_extensional : forall b isEmpty fr ba, HProp_extensional (lseg b isEmpty fr ba).
    destruct isEmpty; reflexivity.
  Qed.

  Theorem queue_extensional : forall b p, HProp_extensional (queue b p).
    reflexivity.
  Qed.

  Theorem queue_fwd : forall b p,
    queue b p
    ===> Ex fr, Ex ba, Ex isEmpty, [| freeable p 2 |] * (p ==*> fr, ba) * lseg' b isEmpty fr ba.
    unfold queue; sepLemma.
  Qed.

  Theorem queue_bwd : forall b p,
    (Ex fr, Ex ba, Ex isEmpty, [| freeable p 2 |] * (p ==*> fr, ba) * lseg' b isEmpty fr ba)
    ===> queue b p.
    unfold queue; sepLemma.
  Qed.

  Theorem lseg'_empty_bwd : forall b isEmpty (fr : W) ba,
    fr = 0
    -> [| isEmpty = true /\ b %= empty |] ===> lseg' b isEmpty fr ba.
    destruct isEmpty; sepLemma.
  Qed.

  Theorem lseg'_empty_fwd : forall b isEmpty (fr : W) ba,
    fr = 0
    -> lseg' b isEmpty fr ba ===> [| isEmpty = true /\ b %= empty |].
    destruct isEmpty; sepLemma.
  Qed.

  Theorem lseg'_nonempty_fwd : forall b isEmpty (fr : W) ba,
    fr <> 0
    -> lseg' b isEmpty fr ba
    ===> [| isEmpty = false |] * Ex v1, Ex v2, Ex n, [| (v1, v2) %in b |] * lseg (b %- (v1, v2)) n fr ba * (ba ==*> v1, v2, $0).
    destruct isEmpty; sepLemma.
  Qed.

  Theorem lseg'_nonempty_bwd : forall b isEmpty (fr : W) ba,
    fr <> 0
    -> [| isEmpty = false |] * (Ex v1, Ex v2, Ex n, [| (v1, v2) %in b |] * lseg (b %- (v1, v2)) n fr ba * (ba ==*> v1, v2, $0))
    ===> lseg' b isEmpty fr ba.
    destruct isEmpty; sepLemma.
  Qed.
End Queue.

Import Queue.
Export Queue.

Hint Immediate lseg_extensional lseg'_extensional queue_extensional.

Definition hints : TacPackage.
  prepare (queue_fwd, lseg'_empty_fwd, lseg'_nonempty_fwd)
  (queue_bwd, lseg'_empty_bwd, lseg'_nonempty_bwd).
Defined.


(** * The code *)

Definition initS := initS queue 7.
Definition isEmptyS := isEmptyS queue 0.

Definition queueM := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "queue" {{
  bfunction "init"("r") [initS]
    "r" <-- Call "malloc"!"malloc"(0)
    [PRE[_, R] R =?> 2 * [| freeable R 2 |]
     POST[R'] [| R' = R |] * queue empty R ];;
    "r" *<- 0;;
    Return "r"
  end with bfunction "isEmpty"("b") [isEmptyS]
    "b" <-* "b";;
    If ("b" = 0) {
      Return 1
    } else {
      Return 0
    }
  end
}}.

Theorem queueMOk : moduleOk queueM.
  vcgen; abstract (sep hints; words).
Qed.
