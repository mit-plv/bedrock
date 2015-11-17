Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.TuplesF.
Require Import Bedrock.Platform.Facade.examples.Tuples1F.


Module Type ADT.
  Parameter tuples2 : W -> W -> W -> tuples -> W -> HProp.
  Parameter tree : W -> W -> W -> skel -> tuples -> W -> HProp.

  Axiom tuples2_fwd : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    ===> [| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
        * [| key1 < len |] * [| key2 < len |].
  Axiom tuples2_bwd : forall len key1 key2 ts (c : W),
    ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
    * [| key1 < len |] * [| key2 < len |])
    ===> tuples2 len key1 key2 ts c.

  (* Sometimes this version is necessary to integrate well with the automation. *)
  Axiom tuples2_eq : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    = ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
        * [| key1 < len |]* [| key2 < len |])%Sep.

  Axiom tree_Equiv : forall len key1 key2 sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key1 key2 sk ts1 p ===> tree len key1 key2 sk ts2 p.

  Axiom tree_leaf_fwd : forall len key1 key2 sk ts (p : W), p = 0
    -> tree len key1 key2 sk ts p ===> [| sk = Leaf |] * [| empty ts |].

  Axiom tree_leaf_bwd : forall len key1 key2 sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key1 key2 sk ts p.

  Axiom tree_node_fwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> tree len key1 key2 sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2,
        [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2.

  Axiom tree_node_bwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2) ===> tree len key1 key2 sk ts p.


  Parameter stack : W -> W -> W -> list (tuples * W) -> W -> HProp.
  (* This last one is used as we walk a tree in full to enumerate. *)

  Axiom stack_nil_fwd : forall len key1 key2 tss (p : W), p = 0
    -> stack len key1 key2 tss p ===> [| tss = nil |].

  Axiom stack_nil_bwd : forall len key1 key2 tss (p : W), p = 0
    -> [| tss = nil |] ===> stack len key1 key2 tss p.

  Axiom stack_cons_fwd : forall len key1 key2 tss (p : W), p <> 0
    -> stack len key1 key2 tss p ===> Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |]
      * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p'.

  Axiom stack_cons_bwd : forall len key1 key2 tss (p : W), p <> 0
    -> (Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |] * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p')
      ===> stack len key1 key2 tss p.
End ADT.

(* ADD THIS (with proof) TO Tuples1F! *)
Axiom tuples1_Equiv : forall len key ts1 ts2 p,
  Equiv ts1 ts2
  -> tuples1 len key ts1 p ===> tuples1 len key ts2 p.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint tree (len key1 key2 : W) (sk : skel) (ts : tuples) (p : W) : HProp :=
    match sk with
    | Leaf => [| p = 0 |] * [| empty ts |]
    | Node sk1 sk2 => [| p <> 0 |]
      * Ex p1, Ex k, Ex t0, Ex p2, (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2
    end.

  Fixpoint stack (len key1 key2 : W) (tss : list (tuples * W)) (p : W) : HProp :=
    match tss with
    | nil => [| p = 0 |]
    | (ts, tp) :: tss' => [| p <> 0 |] * [| freeable p 2 |] * [| functional ts |] * Ex sk, Ex p', (p ==*> tp, p')
                    * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p'
    end.

  Definition tuples2 (len key1 key2 : W) (ts : tuples) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
    * [| key1 < len |] * [| key2 < len |].

  Theorem stack_nil_fwd : forall len key1 key2 tss (p : W), p = 0
    -> stack len key1 key2 tss p ===> [| tss = nil |].
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_nil_bwd : forall len key1 key2 tss (p : W), p = 0
    -> [| tss = nil |] ===> stack len key1 key2 tss p.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_cons_fwd : forall len key1 key2 tss (p : W), p <> 0
    -> stack len key1 key2 tss p ===> Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |]
      * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p'.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_cons_bwd : forall len key1 key2 tss (p : W), p <> 0
    -> (Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |] * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p')
      ===> stack len key1 key2 tss p.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
    injection H0; sepLemma; auto.
    injection H0; sepLemma.
  Qed.

  Theorem tuples2_fwd : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    ===> [| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
    * [| key1 < len |] * [| key2 < len |].
  Proof.
    unfold tuples2; sepLemma; eauto.
  Qed.

  Theorem tuples2_bwd : forall len key1 key2 ts (c : W),
    ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
     * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
     * [| key1 < len |] * [| key2 < len |])
    ===> tuples2 len key1 key2 ts c.
  Proof.
    unfold tuples2; sepLemma; eauto.
  Qed.

  Theorem tuples2_eq : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    = ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
        * [| key1 < len |] * [| key2 < len |])%Sep.
  Proof.
    auto.
  Qed.

  Theorem tree_Equiv : forall len key1 key2 sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key1 key2 sk ts1 p ===> tree len key1 key2 sk ts2 p.
  Proof.
    induction sk; sepLemma.

    Equiv.

    repeat apply himp_star_frame; eauto.
    eapply tuples1_Equiv; eauto.
  Qed.

  Theorem tree_leaf_fwd : forall len key1 key2 sk ts (p : W), p = 0
    -> tree len key1 key2 sk ts p ===> [| sk = Leaf |] * [| empty ts |].
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_leaf_bwd : forall len key1 key2 sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key1 key2 sk ts p.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_fwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> tree len key1 key2 sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2,
        [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_bwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2) ===> tree len key1 key2 sk ts p.
  Proof.
    destruct sk; sepLemma.
    injection H0; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (tuples2_fwd, tree_leaf_fwd, tree_node_fwd, stack_nil_fwd, stack_cons_fwd)
          (tuples2_bwd, tree_leaf_bwd, tree_node_bwd, stack_nil_bwd, stack_cons_bwd).
Defined.

(* Also, we want a way to indicate that the trees in a stack are intact, even though the stack has been freed. *)
Fixpoint stacktrees (len key1 key2 : W) (tss : list (tuples * W)) : HProp :=
  match tss with
  | nil => Emp
  | (ts, tp) :: tss' => (Ex sk, tree len key1 key2 sk ts tp) * stacktrees len key1 key2 tss'
  end%Sep.

Definition newS := SPEC("extra_stack", "len", "key1", "key2") reserving 7
  PRE[V] [| V "len" >= $2 |] * [| V "key1" < V "len" |]  * [| V "key2" < V "len" |] * mallocHeap 0
  POST[R] tuples2 (V "len") (V "key1") (V "key2") Empty R * mallocHeap 0.

Definition insertS := SPEC("extra_stack", "self", "tup") reserving 31
  Al len, Al key1, Al key2, Al ts, Al t, Al ts',
  PRE[V] tuples2 len key1 key2 ts (V "self") * tuple t (V "tup") * [| length t = wordToNat len |] * mallocHeap 0
         * [| insert ts t ts' |]
  POST[R] [| R = $0 |] * tuples2 len key1 key2 ts' (V "self") * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "ArrayTuple"!"get" @ [ArrayTupleF.getS], "TupleList"!"new" @ [TupleListF.newS],
                           "Tuples1"!"new" @ [Tuples1F.newS], "Tuples1"!"insert" @ [Tuples1F.insertS] ]]
  bmodule "Tuples2" {{
    bfunction "new"("extra_stack", "len", "key1", "key2") [newS]
      "extra_stack" <-- Call "malloc"!"malloc"(0, 4)
      [PRE[V, R] R =?> 4 * [| R <> 0 |] * [| freeable R 4 |]
              * [| (V "len" >= $2)%word |] * [| (V "key1" < V "len")%word |] * [| (V "key2" < V "len")%word |]
       POST[R'] tuples2 (V "len") (V "key1") (V "key2") Empty R'];;

      "extra_stack" *<- "len";;
      "extra_stack" + 4 *<- "key1";;
      "extra_stack" + 8 *<- "key2";;
      "extra_stack" + 12 *<- 0;;
      Return "extra_stack"
    end

    with bfunction "insert"("extra_stack", "self", "tup", "len", "key1", "key2", "p", "k1", "k2") [insertS]
      "len" <-* "self";;
      "key1" <-* "self" + 4;;
      "key2" <-* "self" + 8;;
      "self" <- "self" + 12;;
      "p" <-* "self";;
      "k1" <-- Call "ArrayTuple"!"get"("extra_stack", "tup", "key1")
      [Al ts, Al t, Al ts', Al sk,
       PRE[V, R] V "self" =*> V "p" * tree (V "len") (V "key1") (V "key2") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| R = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      [Al ts, Al t, Al ts', Al sk,
       PRE[V] V "self" =*> V "p" * tree (V "len") (V "key1") (V "key2") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0]
      While ("p" <> 0) {
        "k2" <-* "p" + 4;;

        If ("k1" = "k2") {
          (* Found existing node for this key.  Add to its collection. *)
          "k2" <-* "p" + 8;;
          Call "Tuples1"!"insert"("extra_stack", "k2", "tup")
          [PRE[_] Emp
           POST[R] [| R = $0 |] ];;
          Return 0
        } else {
          (* No match.  Proceed to appropriate subtree. *)
          If ("k1" < "k2") {
            "self" <- "p"
          } else {
            "self" <- "p" + 12
          };;
          "p" <-* "self"
        }
      };;

      (* This key hasn't been added yet.  Create a new tree node for it. *)
      "k2" <-- Call "Tuples1"!"new"("extra_stack", "len", "key2")
      [Al ts, Al t, Al ts',
       PRE[V, R] tuples1 (V "len") (V "key2") Empty R * [| empty ts |]
         * V "self" =*> V "p" * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      Call "Tuples1"!"insert"("extra_stack", "k2", "tup")
      [Al ts, Al t, Al ts',
       PRE[V] tuples1 (V "len") (V "key2") ts' (V "k2") * [| empty ts |]
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      "p" <-- Call "malloc"!"malloc"(0, 4)
      [Al ts, Al t, Al ts',
       PRE[V, R] R =?> 4 * [| R <> 0 |] * [| empty ts |]
         * tuples1 (V "len") (V "key2") ts' (V "k2")
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      "p" *<- 0;;
      "p" + 4 *<- "k1";;
      "p" + 8 *<- "k2";;
      "p" + 12 *<- 0;;
      "self" *<- "p";;
      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac descend' := try rewrite tuples2_eq; descend;
                 try match goal with
                     | [ H : insert _ ?b _ |- context[insert _ ?b' _] ] =>
                       unify b b'
                     end.

Ltac tree_cong :=
  try rewrite app_assoc;
  repeat apply himp_star_frame; try ((apply tuples1_Equiv || apply tree_Equiv); solve [ eauto ]);
  descend'; step hints; eauto.

Ltac t := solve [ enterFunction
            || (post; evaluate hints; descend; try unifyLocals; repeat (step hints; descend'); eauto;
                try tree_cong) ].

Theorem ok : moduleOk m.
Proof.
  vcgen.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
Qed.
