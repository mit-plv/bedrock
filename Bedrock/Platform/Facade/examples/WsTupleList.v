Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TuplesF Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.WSTuple.


Module Type ADT.
  Parameter wlseq : list WSTupl -> W -> HProp.
  Parameter wlseq' : list WSTupl -> W -> HProp.

  Axiom wlseq_fwd : forall ls c, wlseq ls c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * wlseq' ls p.
  Axiom wlseq_bwd : forall ls (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * wlseq' ls p) ===> wlseq ls c.

  Axiom wlseq'_empty_fwd : forall ls (c : W), c = 0
    -> wlseq' ls c
    ===> [| ls = nil |].

  Axiom wlseq'_empty_bwd : forall ls (c : W), c = 0
    -> [| ls = nil |] ===> wlseq' ls c.

  Axiom wlseq'_nonempty_fwd : forall ls (c : W), c <> 0
    -> wlseq' ls c
    ===> Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * wlseq' ls' p' * wstuple xt x.

  Axiom wlseq'_nonempty_bwd : forall ls (c : W), c <> 0
    -> (Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * wlseq' ls' p' * wstuple xt x) ===> wlseq' ls c.

  Axiom wlseq'_nil_fwd : forall (c : W),
    wlseq' nil c
    ===> [| c = 0 |].

  Axiom wlseq'_cons_fwd : forall xt ls (c : W),
    wlseq' (xt :: ls) c
    ===> [| c <> 0 |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p') * wlseq' ls p' * wstuple xt x.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint wlseq' (ls : list WSTupl) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | xt :: ls' => [| p <> 0 |] * [| freeable p 2 |]
        * Ex x, Ex p', (p ==*> x, p')
        * wlseq' ls' p' * wstuple xt x
    end.

  Definition wlseq (ls : list WSTupl) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * wlseq' ls p.

  Theorem wlseq_fwd : forall ls c, wlseq ls c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * wlseq' ls p.
  Proof.
    unfold wlseq; sepLemma.
  Qed.

  Theorem wlseq_bwd : forall ls (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * wlseq' ls p) ===> wlseq ls c.
  Proof.
    unfold wlseq; sepLemma.
  Qed.

  Theorem wlseq'_empty_fwd : forall ls (c : W), c = 0
    -> wlseq' ls c
    ===> [| ls = nil |].
  Proof.
    destruct ls; sepLemma.
  Qed.

  Theorem wlseq'_empty_bwd : forall ls (c : W), c = 0
    -> [| ls = nil |] ===> wlseq' ls c.
  Proof.
    destruct ls; sepLemma.
  Qed.

  Theorem wlseq'_nonempty_fwd : forall ls (c : W), c <> 0
    -> wlseq' ls c
    ===> Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * wlseq' ls' p' * wstuple xt x.
  Proof.
    destruct ls; sepLemma.
  Qed.

  Theorem wlseq'_nonempty_bwd : forall ls (c : W), c <> 0
    -> (Ex xt, Ex ls', [| ls = xt :: ls' |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p')
        * wlseq' ls' p' * wstuple xt x) ===> wlseq' ls c.
  Proof.
    destruct ls; sepLemma.
    injection H0; sepLemma.
  Qed.

  Theorem wlseq'_nil_fwd : forall (c : W),
    wlseq' nil c
    ===> [| c = 0 |].
  Proof.
    sepLemma.
  Qed.

  Theorem wlseq'_cons_fwd : forall xt ls (c : W),
    wlseq' (xt :: ls) c
    ===> [| c <> 0 |] * [| freeable c 2 |] * Ex x, Ex p', (c ==*> x, p') * wlseq' ls p' * wstuple xt x.
  Proof.
    sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (wlseq_fwd, wlseq'_empty_fwd, wlseq'_nonempty_fwd, wlseq'_nil_fwd, wlseq'_cons_fwd)
  (wlseq_bwd, wlseq'_empty_bwd, wlseq'_nonempty_bwd).
Defined.

Definition newS := SPEC("extra_stack") reserving 8
  PRE[_] mallocHeap 0
  POST[R] wlseq nil R * mallocHeap 0.

Definition deleteS := SPEC("extra_stack", "self") reserving 6
  PRE[V] wlseq nil (V "self") * mallocHeap 0
  POST[R] [| R = $0 |] * mallocHeap 0.

Definition copyS := SPEC("extra_stack", "self", "len") reserving 27
  Al ls,
  PRE[V] wlseq ls (V "self") * [| allTuplesLen (wordToNat (V "len")) ls |] * [| $2 <= V "len" |] * mallocHeap 0
  POST[R] wlseq ls (V "self") * wlseq ls R * mallocHeap 0.

Definition copyAppendS := SPEC("extra_stack", "self", "other", "len") reserving 27
  Al ls1, Al ls2,
  PRE[V] wlseq ls1 (V "self") * wlseq ls2 (V "other") * [| $2 <= V "len" |] * mallocHeap 0
    * [| allTuplesLen (wordToNat (V "len")) ls1 |]
  POST[R] [| R = $0 |] * wlseq ls1 (V "self") * wlseq (ls1 ++ ls2) (V "other") * mallocHeap 0.

Definition popS := SPEC("extra_stack", "self") reserving 8
  Al x, Al ls,
  PRE[V] wlseq (x :: ls) (V "self") * mallocHeap 0
  POST[R] wstuple x R * wlseq ls (V "self") * mallocHeap 0.

Definition emptyS := SPEC("extra_stack", "self") reserving 0
  Al ls,
  PRE[V] wlseq ls (V "self") * mallocHeap 0
  POST[R] [| (ls = nil) \is R |] * wlseq ls (V "self") * mallocHeap 0.

Definition pushS := SPEC("extra_stack", "self", "tup") reserving 8
  Al ls, Al tup,
  PRE[V] wlseq ls (V "self") * wstuple tup (V "tup") * mallocHeap 0
  POST[R] [| R = $0 |] * wlseq (tup :: ls) (V "self") * mallocHeap 0.

Definition revS := SPEC("extra_stack", "self") reserving 2
  Al ls,
  PRE[V] wlseq ls (V "self") * mallocHeap 0
  POST[R] [| R = $0 |] * wlseq (rev ls) (V "self") * mallocHeap 0.

Definition lengthS := SPEC("extra_stack", "self") reserving 1
  Al ls,
  PRE[V] wlseq ls (V "self") * mallocHeap 0
  POST[R] [| R = $ (length ls) |] * wlseq ls (V "self") * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "WSTuple"!"copy" @ [WSTuple.copyS] ]]
  bmodule "TupleList" {{
    bfunction "new"("extra_stack", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[_, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0
       POST[R'] wlseq nil R' * mallocHeap 0];;

      "x" *<- 0;;
      Return "x"
    end

    with bfunction "delete"("extra_stack", "self") [deleteS]
      Call "malloc"!"free"(0, "self", 2)
      [PRE[_] Emp
       POST[R] [| R = $0 |] ];;
      Return 0
    end

    with bfunction "copy"("extra_stack", "self", "len", "new", "acc", "tmp") [copyS]
      "self" <-* "self";;

      "new" <-- Call "malloc"!"malloc"(0, 2)
      [Al ls,
       PRE[V, R] wlseq' ls (V "self") * [| allTuplesLen (wordToNat (V "len")) ls |] * [| ($2 <= V "len")%word |] * R =?> 1 * mallocHeap 0
       POST[R'] [| R' = R |] * wlseq' ls (V "self") * Ex p, R =*> p * wlseq' ls p * mallocHeap 0];;
      "acc" <- "new";;

      [Al ls,
       PRE[V] wlseq' ls (V "self") * [| allTuplesLen (wordToNat (V "len")) ls |] * [| ($2 <= V "len")%word |] * V "acc" =?> 1 * mallocHeap 0
       POST[R] [| R = V "new" |] * wlseq' ls (V "self") * Ex p, V "acc" =*> p * wlseq' ls p * mallocHeap 0]
      While ("self" <> 0) {
        "tmp" <-* "self";;
        "self" <-* "self"+4;;

        "extra_stack" <-- Call "malloc"!"malloc"(0, 2)
        [Al xt, Al ls,
         PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
                 * wlseq' ls (V "self") * wstuple xt (V "tmp")
                 * [| length xt = wordToNat (V "len") |] * [| allTuplesLen (wordToNat (V "len")) ls |]
                 * [| ($2 <= V "len")%word |] * V "acc" =?> 1 * mallocHeap 0
         POST[R'] [| R' = V "new" |] * wlseq' ls (V "self") * Ex p, V "acc" =*> p
                * wlseq' (xt :: ls) p * wstuple xt (V "tmp") * mallocHeap 0];;

        "tmp" <-- Call "WSTuple"!"copy"("extra_stack", "tmp", "len")
        [Al xt, Al ls,
         PRE[V, R] wstuple xt R
                 * V "extra_stack" =?> 2 * [| V "extra_stack" <> 0 |] * [| freeable (V "extra_stack") 2 |]
                 * wlseq' ls (V "self")
                 * [| length xt = wordToNat (V "len") |] * [| allTuplesLen (wordToNat (V "len")) ls |]
                 * [| ($2 <= V "len")%word |] * V "acc" =?> 1 * mallocHeap 0
         POST[R'] [| R' = V "new" |] * wlseq' ls (V "self") * Ex p, V "acc" =*> p
                * wlseq' (xt :: ls) p * mallocHeap 0];;

        "acc" *<- "extra_stack";;
        "extra_stack" *<- "tmp";;
        "acc" <- "extra_stack"+4
      };;

      "acc" *<- 0;;
      Return "new"
    end

    with bfunction "copyAppend"("extra_stack", "self", "other", "len", "new", "acc", "tmp") [copyAppendS]
      "self" <-* "self";;
      "acc" <- "other";;
      "other" <-* "other";;

      [Al ls1, Al ls2,
       PRE[V] wlseq' ls1 (V "self") * [| allTuplesLen (wordToNat (V "len")) ls1 |] * [| ($2 <= V "len")%word |] * V "acc" =?> 1 * wlseq' ls2 (V "other") * mallocHeap 0
       POST[R] [| R = $0 |] * wlseq' ls1 (V "self") * Ex p, V "acc" =*> p * wlseq' (ls1 ++ ls2) p * mallocHeap 0]
      While ("self" <> 0) {
        "tmp" <-* "self";;
        "self" <-* "self"+4;;

        "extra_stack" <-- Call "malloc"!"malloc"(0, 2)
        [Al xt, Al ls1, Al ls2,
         PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
                 * wlseq' ls1 (V "self") * wstuple xt (V "tmp")
                 * [| length xt = wordToNat (V "len") |] * [| allTuplesLen (wordToNat (V "len")) ls1 |]
                 * [| ($2 <= V "len")%word |] * V "acc" =?> 1 * wlseq' ls2 (V "other") * mallocHeap 0
         POST[R'] [| R' = $0 |] * wlseq' ls1 (V "self") * Ex p, V "acc" =*> p
                * wlseq' (xt :: ls1 ++ ls2) p * wstuple xt (V "tmp") * mallocHeap 0];;

        "tmp" <-- Call "WSTuple"!"copy"("extra_stack", "tmp", "len")
        [Al xt, Al ls1, Al ls2,
         PRE[V, R] wstuple xt R
                 * V "extra_stack" =?> 2 * [| V "extra_stack" <> 0 |] * [| freeable (V "extra_stack") 2 |]
                 * wlseq' ls1 (V "self")
                 * [| length xt = wordToNat (V "len") |] * [| allTuplesLen (wordToNat (V "len")) ls1 |]
                 * [| ($2 <= V "len")%word |] * V "acc" =?> 1 * wlseq' ls2 (V "other") * mallocHeap 0
         POST[R'] [| R' = $0 |] * wlseq' ls1 (V "self") * Ex p, V "acc" =*> p
                * wlseq' (xt :: ls1 ++ ls2) p * mallocHeap 0];;

        "acc" *<- "extra_stack";;
        "extra_stack" *<- "tmp";;
        "acc" <- "extra_stack"+4
      };;

      "acc" *<- "other";;
      Return 0
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
       PRE[V] wlseq' ls (V "self")
       POST[R] [| R = V "acc" ^+ $ (length ls) |] * wlseq' ls (V "self") ]
      While ("self" <> 0) {
        "acc" <- "acc" + 1;;
        "self" <-* "self"+4
      };;

      Return "acc"

    end with bfunction "rev"("extra_stack", "self", "from", "to") [revS]
      "from" <-* "self";;
      "to" <- 0;;

      [Al ls, Al ls',
       PRE[V] V "self" =?> 1 * wlseq' ls (V "from") * wlseq' ls' (V "to")
       POST[R] [| R = $0 |] * Ex p, V "self" =*> p * wlseq' (rev_append ls ls') p]
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
  vcgen; abstract (sep hints; try fold (@length WS); eauto; try rewrite natToW_S; try rewrite <- rev_alt; eauto; step auto_ext).
Qed.
