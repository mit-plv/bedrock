Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.


Module Type ADT.
  Parameter lseq : list (list W) -> W -> HProp.
  Parameter lseq' : list (list W) -> W -> HProp.

  Axiom lseq_fwd : forall ls c, lseq ls c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p.
  Axiom lseq_bwd : forall ls (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p) ===> lseq ls c.

  Axiom lseq'_empty_fwd : forall ls (c : W), c = 0
    -> lseq' ls c
    ===> [| ls = nil |].

  Axiom lseq'_empty_bwd : forall ls (c : W), c = 0
    -> [| ls = nil |] ===> lseq' ls c.

  Axiom lseq'_nonempty_fwd : forall ls (c : W), c <> 0
    -> lseq' ls c
    ===> Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * lseq' ls' p' * tuple xt x.

  Axiom lseq'_nonempty_bwd : forall ls (c : W), c <> 0
    -> (Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * lseq' ls' p' * tuple xt x) ===> lseq' ls c.

  Axiom lseq'_cons_fwd : forall xt ls (c : W),
    lseq' (xt :: ls) c
    ===> [| c <> 0 |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p') * lseq' ls p' * tuple xt x.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint lseq' (ls : list (list W)) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | xt :: ls' => [| p <> 0 |] * [| freeable p 2 |]
        * Ex x, Ex p', (p ==*> x, p')
        * lseq' ls' p' * tuple xt x
    end.

  Definition lseq (ls : list (list W)) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p.

  Theorem lseq_fwd : forall ls c, lseq ls c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p.
  Proof.
    unfold lseq; sepLemma.
  Qed.

  Theorem lseq_bwd : forall ls (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p) ===> lseq ls c.
  Proof.
    unfold lseq; sepLemma.
  Qed.

  Theorem lseq'_empty_fwd : forall ls (c : W), c = 0
    -> lseq' ls c
    ===> [| ls = nil |].
  Proof.
    destruct ls; sepLemma.
  Qed.

  Theorem lseq'_empty_bwd : forall ls (c : W), c = 0
    -> [| ls = nil |] ===> lseq' ls c.
  Proof.
    destruct ls; sepLemma.
  Qed.

  Theorem lseq'_nonempty_fwd : forall ls (c : W), c <> 0
    -> lseq' ls c
    ===> Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * lseq' ls' p' * tuple xt x.
  Proof.
    destruct ls; sepLemma.
  Qed.

  Theorem lseq'_nonempty_bwd : forall ls (c : W), c <> 0
    -> (Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * lseq' ls' p' * tuple xt x) ===> lseq' ls c.
  Proof.
    destruct ls; sepLemma.
    injection H0; sepLemma.
  Qed.

  Theorem lseq'_cons_fwd : forall xt ls (c : W),
    lseq' (xt :: ls) c
    ===> [| c <> 0 |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p') * lseq' ls p' * tuple xt x.
  Proof.
    sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (lseq_fwd, lseq'_empty_fwd, lseq'_nonempty_fwd, lseq'_cons_fwd)
  (lseq_bwd, lseq'_empty_bwd, lseq'_nonempty_bwd).
Defined.

Definition newS := newS lseq 8.
Definition popS := popS tuple lseq 8.
Definition emptyS := emptyS lseq 0.
Definition pushS := pushS tuple lseq 8.
Definition revS := revS lseq 2.
Definition lengthS := lengthS lseq 1.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ListSeq" {{
    bfunction "new"("extra_stack", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[_, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0
       POST[R'] lseq nil R' * mallocHeap 0];;

      "x" *<- 0;;
      Return "x"
    end

    with bfunction "pop"("extra_stack", "self", "tmp", "r") [popS]
      "tmp" <-* "self";;
      "r" <-* "tmp";;
      "extra_stack" <-* "tmp"+4;;
      "self" *<- "extra_stack";;

      Call "malloc"!"free"(0, "tmp", 2)
      [PRE[V] Emp
       POST[R] [| R = V "r" |] ];;

      Return "r"
    end

    with bfunction "empty"("extra_stack", "self") [emptyS]
      "self" <-* "self";;

      If ("self" = 0) {
        Return 1
      } else {
        Return 0
      }
    end

    with bfunction "push"("extra_stack", "self", "tup", "tmp") [pushS]
      "tmp" <-- Call "malloc"!"malloc"(0, 2)
      [Al p,
       PRE[V, R] V "self" =*> p * R =?> 2
       POST[R'] [| R' = $0 |] * V "self" =*> R * (R ==*> V "tup", p) ];;

      "tmp" *<- "tup";;
      "extra_stack" <-* "self";;
      "tmp"+4 *<- "extra_stack";;
      "self" *<- "tmp";;
      Return 0
    end

    with bfunction "length"("extra_stack", "self", "acc") [lengthS]
      "self" <-* "self";;
      "acc" <- 0;;

      [Al ls,
       PRE[V] lseq' ls (V "self")
       POST[R] [| R = V "acc" ^+ $ (length ls) |] * lseq' ls (V "self") ]
      While ("self" <> 0) {
        "acc" <- "acc" + 1;;
        "self" <-* "self"+4
      };;

      Return "acc"

    end with bfunction "rev"("extra_stack", "self", "from", "to") [revS]
      "from" <-* "self";;
      "to" <- 0;;

      [Al ls, Al ls',
       PRE[V] V "self" =?> 1 * lseq' ls (V "from") * lseq' ls' (V "to")
       POST[R] [| R = $0 |] * Ex p, V "self" =*> p * lseq' (rev_append ls ls') p]
      While ("from" <> 0) {
        "extra_stack" <-* "from"+4;;
        "from"+4 *<- "to";;
        "to" <- "from";;
        "from" <- "extra_stack"
      };;

      "self" *<- "to";;
      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Theorem ok : moduleOk m.
Proof.
  vcgen; abstract (sep hints; eauto; try rewrite natToW_S; try rewrite <- rev_alt; eauto; step auto_ext).
Qed.
