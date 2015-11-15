Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.TuplesF.
Require Import Bedrock.Platform.Facade.examples.Tuples0F.

Inductive skel :=
| Leaf
| Node (sk1 sk2 : skel).

Definition keepEq (ts : tuples) (key k : W) : tuples :=
  fun tup => Ensembles.In _ ts tup /\ Array.sel (indexedElement tup) key = k.
Definition keepLt (ts : tuples) (key k : W) : tuples :=
  fun tup => Ensembles.In _ ts tup /\ Array.sel (indexedElement tup) key < k.
Definition keepGt (ts : tuples) (key k : W) : tuples :=
  fun tup => Ensembles.In _ ts tup /\ Array.sel (indexedElement tup) key > k.
Definition empty (ts : tuples) := forall t, ~Ensembles.In _ ts t.

Module Type ADT.
  Parameter tuples1 : W -> tuples -> W -> HProp.
  Parameter tree : W -> W -> skel -> tuples -> W -> HProp.

  Axiom tuples1_fwd : forall len ts c, tuples1 len ts c
    ===> [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
        * Ex key, Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].
  Axiom tuples1_bwd : forall len ts (c : W),
    ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex key, Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])
    ===> tuples1 len ts c.

  Axiom tree_leaf_fwd : forall len key sk ts (p : W), p = 0
    -> tree len key sk ts p ===> [| sk = Leaf |] * [| empty ts |].

  Axiom tree_leaf_bwd : forall len key sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key sk ts p.

  Axiom tree_node_fwd : forall len key sk ts (p : W), p <> 0
    -> tree len key sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2.

  Axiom tree_node_bwd : forall len key sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2) ===> tree len key sk ts p.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint tree (len key : W) (sk : skel) (ts : tuples) (p : W) : HProp :=
    match sk with
    | Leaf => [| p = 0 |] * [| empty ts |]
    | Node sk1 sk2 => [| p <> 0 |]
      * Ex p1, Ex k, Ex t0, Ex p2, (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2
    end.

  Definition tuples1 (len : W) (ts : tuples) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex key, Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].

  Theorem tuples1_fwd : forall len ts c, tuples1 len ts c
    ===> [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex key, Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].
  Proof.
    unfold tuples1; sepLemma.
  Qed.

  Theorem tuples1_bwd : forall len ts (c : W),
    ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
     * Ex key, Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])
    ===> tuples1 len ts c.
  Proof.
    unfold tuples1; sepLemma.
  Qed.

  Theorem tree_leaf_fwd : forall len key sk ts (p : W), p = 0
    -> tree len key sk ts p ===> [| sk = Leaf |] * [| empty ts |].
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_leaf_bwd : forall len key sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key sk ts p.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_fwd : forall len key sk ts (p : W), p <> 0
    -> tree len key sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_bwd : forall len key sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2) ===> tree len key sk ts p.
  Proof.
    destruct sk; sepLemma.
    injection H0; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (tuples1_fwd, tree_leaf_fwd, tree_node_fwd)
          (tuples1_bwd, tree_leaf_bwd, tree_node_bwd).
Defined.

Definition newS := SPEC("extra_stack", "len", "key") reserving 7
  PRE[V] [| V "len" >= $2 |] * [| V "key" < V "len" |] * mallocHeap 0
  POST[R] tuples1 (V "len") Empty R * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "Tuples1" {{
    bfunction "new"("extra_stack", "len", "key") [newS]
      "extra_stack" <-- Call "malloc"!"malloc"(0, 3)
      [PRE[V, R] R =?> 3 * [| R <> 0 |] * [| freeable R 3 |]
              * [| (V "len" >= $2)%word |] * [| (V "key" < V "len")%word |]
       POST[R'] tuples1 (V "len") Empty R'];;

      "extra_stack" *<- "len";;
      "extra_stack" + 4 *<- "key";;
      "extra_stack" + 8 *<- 0;;
      Return "extra_stack"
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma empty_Empty : empty Empty.
Proof.
  hnf; intuition.
Qed.

Hint Resolve empty_Empty.

Theorem ok : moduleOk m.
Proof.
  vcgen.

  Ltac t := sep hints; eauto.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
Qed.
