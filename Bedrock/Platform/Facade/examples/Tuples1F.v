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

Definition replaceKey (ts ts' : tuples) (key k : W) : tuples :=
  fun t => IF Array.sel (indexedElement t) key = k then ts' t else ts t.

Definition bounded (ts : tuples) := exists bound, UnConstrFreshIdx ts bound.

Ltac Equiv' := unfold bounded, insert, EnsembleInsert, Equiv, replaceKey, IF_then_else,
               keepEq, keepLt, keepGt, empty, Ensembles.In, UnConstrFreshIdx in *.
Ltac Equiv := Equiv'; firstorder idtac.

Theorem keepEq_Equiv : forall ts1 ts2 key k,
  Equiv ts1 ts2
  -> Equiv (keepEq ts1 key k) (keepEq ts2 key k).
Proof.
  Equiv.
Qed.

Theorem keepLt_Equiv : forall ts1 ts2 key k,
  Equiv ts1 ts2
  -> Equiv (keepLt ts1 key k) (keepLt ts2 key k).
Proof.
  Equiv.
Qed.

Theorem keepGt_Equiv : forall ts1 ts2 key k,
  Equiv ts1 ts2
  -> Equiv (keepGt ts1 key k) (keepGt ts2 key k).
Proof.
  Equiv.
Qed.

Hint Immediate keepEq_Equiv keepLt_Equiv keepGt_Equiv.

Lemma Equiv_keepEq_replaceKey : forall k1 k ts key ts',
  k1 < k
  -> Equiv (keepEq ts key k) (keepEq (replaceKey ts ts' key k1) key k).
Proof.
  Equiv.
  subst; right; intuition.
  subst; nomega.
  subst; nomega.
Qed.

Hint Immediate Equiv_keepEq_replaceKey.

Lemma Equiv_keepGt_replaceKey_lt : forall k1 k ts key ts',
  k1 < k
  -> Equiv (keepGt ts' key k) (keepGt (replaceKey ts' ts key k1) key k).
Proof.
  Equiv.
  right; intuition.
  subst; nomega.
  subst; nomega.
Qed.

Hint Immediate Equiv_keepGt_replaceKey_lt.

(*Lemma Equiv_keepLt_replaceKey_lt : forall k1 k ts key ts' t,
  k1 < k
  -> insert (keepLt ts' key k) t ts
  -> k1 = Array.sel t key
  -> Equiv ts (keepLt (replaceKey ts' ts key k1) key k).
Proof.
  Equiv'.
  intuition subst.

  destruct H0; intuition subst.
  specialize (proj1 (H3 _) H2).
  intuition (subst; simpl in * ).
  tauto.  
  destruct (weq (Array.sel (indexedElement t0) key) (Array.sel t key)); tauto.

  destruct H0; intuition subst.
  specialize (proj1 (H3 _) H2).
  intuition (subst; simpl in * ).
  tauto.

  destruct H0; intuition subst.
  apply H2; tauto.
Qed.

Hint Immediate Equiv_keepLt_replaceKey_lt.

Lemma bounded_insert : forall ts t ts',
  insert ts t ts'
  -> bounded ts
  -> bounded ts'.
Proof.
  Equiv.
  exists (S (max x x0)).
  intros.
  apply H1 in H2; intuition (subst; simpl).
  specialize (Max.max_spec x x0); intuition.
  apply H in H3.
  specialize (Max.max_spec x x0); intuition.
Qed.

Hint Immediate bounded_insert.*)

(*Lemma insert_replaceKey_lt : forall k1 k ts key ts' t,
  k1 < k
  -> insert (keepLt ts key k) t ts'
  -> k1 = Array.sel t key
  -> bounded ts
  -> insert ts t (replaceKey ts ts' key k1).
Proof.
  Equiv'; intuition subst.
  destruct H0, H2; intuition.
  exists (max x x0); intuition (subst; simpl in * ).
  apply H1 in H0; specialize (Max.max_spec x x0); intuition.
  apply H3 in H5; intuition (subst; simpl in * ).

  unfold EnsembleInsert in *; intuition subst.

  unfold insert.
  unfold EnsembleInsert.

  intuition (subst; simpl in * ).
  tauto.
  destruct (weq (Array.sel (indexedElement t0) key) (Array.sel t key)); tauto.

  intuition (subst; simpl in * ); auto.

  tauto.
Qed.*)


Module Type ADT.
  Parameter tuples1 : W -> W -> tuples -> W -> HProp.
  Parameter tree : W -> W -> skel -> tuples -> W -> HProp.

  Axiom tuples1_fwd : forall len key ts c, tuples1 len key ts c
    ===> [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].
  Axiom tuples1_bwd : forall len key ts (c : W),
    ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])
    ===> tuples1 len key ts c.

  Axiom tree_Equiv : forall len key sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key sk ts1 p ===> tree len key sk ts2 p.

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

  Definition tuples1 (len key : W) (ts : tuples) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].

  Theorem tuples1_fwd : forall len key ts c, tuples1 len key ts c
    ===> [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].
  Proof.
    unfold tuples1; sepLemma; eauto.
  Qed.

  Theorem tuples1_bwd : forall len key ts (c : W),
    ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
     * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])
    ===> tuples1 len key ts c.
  Proof.
    unfold tuples1; sepLemma; eauto.
  Qed.

  Theorem tree_Equiv : forall len key sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key sk ts1 p ===> tree len key sk ts2 p.
  Proof.
    induction sk; sepLemma.

    Equiv.

    repeat apply himp_star_frame; eauto.
    eapply tuples0_Equiv; eauto.
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
  POST[R] tuples1 (V "len") (V "key") Empty R * mallocHeap 0.

Definition insertS := SPEC("extra_stack", "self", "tup") reserving 21
  Al len, Al key, Al ts, Al t, Al ts',
  PRE[V] tuples1 len key ts (V "self") * tuple t (V "tup") * [| length t = wordToNat len |] * mallocHeap 0
         * [| insert ts t ts' |]
  POST[R] [| R = $0 |] * tuples1 len key ts' (V "self") * mallocHeap 0.

Definition grabInserted (ts ts' : tuples) : tuples :=
  fun t => Ensembles.In _ ts' t /\ ~Ensembles.In _ ts t.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "ArrayTuple"!"get" @ [ArrayTupleF.getS],
                           "Tuples0"!"new" @ [Tuples0F.newS], "Tuples0"!"insert" @ [Tuples0F.insertS] ]]
  bmodule "Tuples1" {{
    bfunction "new"("extra_stack", "len", "key") [newS]
      "extra_stack" <-- Call "malloc"!"malloc"(0, 3)
      [PRE[V, R] R =?> 3 * [| R <> 0 |] * [| freeable R 3 |]
              * [| (V "len" >= $2)%word |] * [| (V "key" < V "len")%word |]
       POST[R'] tuples1 (V "len") (V "key") Empty R'];;

      "extra_stack" *<- "len";;
      "extra_stack" + 4 *<- "key";;
      "extra_stack" + 8 *<- 0;;
      Return "extra_stack"
    end

    (*with bfunction "insert"("extra_stack", "self", "tup", "len", "key", "p", "k1", "k2") [insertS]
      "len" <-* "self";;
      "key" <-* "self" + 4;;
      "self" <- "self" + 8;;
      "p" <-* "self";;
      "k1" <-- Call "ArrayTuple"!"get"("extra_stack", "tup", "key")
      [Al ts, Al t, Al ts', Al sk,
       PRE[V, R] V "self" =*> V "p" * tree (V "len") (V "key") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| R = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      [Al ts, Al t, Al ts', Al sk,
       PRE[V] V "self" =*> V "p" * tree (V "len") (V "key") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0]
      While ("p" <> 0) {
        "k2" <-* "p" + 4;;

        If ("k1" = "k2") {
          (* Found existing node for this key.  Add to its collection. *)
          "k2" <-* "p" + 8;;
          Call "Tuples0"!"insert"("extra_stack", "k2", "tup")
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
      "k2" <-- Call "Tuples0"!"new"("extra_stack", "len")
      [Al ts, Al t, Al ts',
       PRE[V, R] tuples0 (V "len") Empty R * [| empty ts |]
         * V "self" =*> V "p" * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      Call "Tuples0"!"insert"("extra_stack", "k2", "tup")
      [Al ts, Al t, Al ts',
       PRE[V] tuples0 (V "len") ts' (V "k2") * [| empty ts |]
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      "p" <-- Call "malloc"!"malloc"(0, 4)
      [Al ts, Al t, Al ts',
       PRE[V, R] R =?> 4 * [| R <> 0 |] * [| empty ts |]
         * tuples0 (V "len") ts' (V "k2")
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      "p" *<- 0;;
      "p" + 4 *<- "k1";;
      "p" + 8 *<- "k2";;
      "p" + 12 *<- 0;;
      "self" *<- "p";;
      Return 0
    end*)
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma empty_Empty : empty Empty.
Proof.
  hnf; intuition.
Qed.

Hint Resolve empty_Empty.

Lemma bounded_keepLt : forall ts key k,
  bounded ts
  -> bounded (keepLt ts key k).
Proof.
  Equiv.
Qed.

Hint Immediate bounded_keepLt.

Lemma insert_keepLt : forall ts t ts' key k1 k,
  insert ts t ts'
  -> k1 = Array.sel t key
  -> k1 < k
  -> insert (keepLt ts key k) t (keepLt ts' key k).
Proof.
  Equiv.
  subst; simpl.
  exists x; intuition (subst; simpl in *; auto).
  apply H2 in H3; intuition (subst; simpl in * ).
  apply H2; tauto.
  firstorder.
Qed.

Hint Immediate insert_keepLt.

Lemma Equiv_keepEq_lt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k1 <> k
  -> k1 = Array.sel t key
  -> Equiv (keepEq ts key k) (keepEq ts' key k).
Proof.
  Equiv.
  subst.
  apply H2 in H3; intuition (subst; simpl in * ).
  tauto.
Qed.

Hint Immediate Equiv_keepEq_lt.

Lemma Equiv_keepGt_lt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k1 < k
  -> k1 = Array.sel t key
  -> Equiv (keepGt ts key k) (keepGt ts' key k).
Proof.
  Equiv.
  subst.
  apply H2 in H3; intuition (subst; simpl in * ).
  nomega.
Qed.

Hint Immediate Equiv_keepGt_lt.

Lemma Equiv_keepEq_gt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k1 <> k
  -> k1 = Array.sel t key
  -> Equiv (keepEq ts key k) (keepEq ts' key k).
Proof.
  Equiv.
  subst.
  apply H2 in H3; intuition (subst; simpl in * ).
  tauto.
Qed.

Hint Immediate Equiv_keepEq_lt.

Lemma Equiv_keepLt_gt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k <= k1
  -> k1 <> k
  -> k1 = Array.sel t key
  -> Equiv (keepLt ts key k) (keepLt ts' key k).
Proof.
  Equiv.
  subst.
  apply H3 in H4; intuition (subst; simpl in * ).
  tauto.
Qed.

Hint Immediate Equiv_keepLt_gt.

Lemma insert_keepGt : forall ts t ts' key k1 k,
  insert ts t ts'
  -> k1 = Array.sel t key
  -> k <= k1
  -> k1 <> k
  -> insert (keepGt ts key k) t (keepGt ts' key k).
Proof.
  Equiv.
  subst; simpl.
  exists x; intuition (subst; simpl in *; auto).
  apply H3 in H4; intuition (subst; simpl in * ).
  apply H3; tauto.
  destruct (weq (Array.sel t key) k); intuition.
  firstorder.
Qed.

Hint Immediate insert_keepGt.

Lemma insert_keepEq : forall ts t ts' key k1,
  insert ts t ts'
  -> k1 = Array.sel t key
  -> insert (keepEq ts key k1) t (keepEq ts' key k1).
Proof.
  Equiv.
  subst; simpl.
  exists x; intuition (subst; simpl in *; auto).
  apply H1 in H2; intuition (subst; simpl in * ).
  apply H1; tauto.
  firstorder.
Qed.

Hint Immediate insert_keepEq.

Lemma Equiv_keepLt_eq : forall k ts key ts' t,
  insert ts t ts'
  -> k = Array.sel t key
  -> Equiv (keepLt ts key k) (keepLt ts' key k).
Proof.
  Equiv.
  subst.
  apply H1 in H2; intuition (subst; simpl in * ).
  nomega.
Qed.

Lemma Equiv_keepGt_eq : forall k ts key ts' t,
  insert ts t ts'
  -> k = Array.sel t key
  -> Equiv (keepGt ts key k) (keepGt ts' key k).
Proof.
  Equiv.
  subst.
  apply H1 in H2; intuition (subst; simpl in * ).
  nomega.
Qed.

Hint Immediate Equiv_keepLt_eq Equiv_keepGt_eq.

Lemma insert_empty_Empty : forall ts t ts',
  empty ts
  -> insert ts t ts'
  -> insert Empty t ts'.
Proof.
  Equiv.
Qed.

Hint Immediate insert_empty_Empty.

Theorem keepEq_eq : forall ts t ts' key k,
  insert ts t ts'
  -> empty ts
  -> k = Array.sel t key
  -> Equiv ts' (keepEq ts' key k).
Proof.
  Equiv.
  apply H2 in H3; intuition (subst; simpl in * ).
  tauto.
  firstorder.
Qed.

Hint Immediate keepEq_eq.

Theorem empty_keepLt : forall ts t ts' key k1,
  insert ts t ts'
  -> empty ts
  -> k1 = Array.sel t key
  -> empty (keepLt ts' key k1).
Proof.
  Equiv.
  intuition.
  apply H2 in H4; intuition (subst; simpl in * ).
  nomega.
  eauto.
Qed.

Theorem empty_keepGt : forall ts t ts' key k1,
  insert ts t ts'
  -> empty ts
  -> k1 = Array.sel t key
  -> empty (keepGt ts' key k1).
Proof.
  Equiv.
  intuition.
  apply H2 in H4; intuition (subst; simpl in * ).
  nomega.
  eauto.
Qed.

Hint Immediate empty_keepLt empty_keepGt.

Theorem ok : moduleOk m.
Proof.
  vcgen.

  Ltac unifyLocals :=
    match goal with
    | [ _ : interp _ (![?P1] ?x) |- interp _ (![?P2] ?x) ] =>
      match P1 with
      | context[locals _ ?vs1 ?y _] =>
        match P2 with
        | context[locals _ ?vs2 y _] => unify vs1 vs2; descend
        end
      end
    | [ |- interp _ (![?P1] ?x ---> ![?P2] ?x)%PropX ] =>
      match P1 with
      | context[locals ?y ?vs1 _ _] =>
        match P2 with
        | context[locals y ?vs2 _ _] => unify vs1 vs2; descend
        end
      end
    end.

  Ltac descend' := descend;
                  try match goal with
                      | [ H : insert _ ?b _ |- context[insert _ ?b' _] ] =>
                        unify b b'
                      end.

  Ltac tree_cong :=
    repeat apply himp_star_frame; try ((apply tuples0_Equiv || apply tree_Equiv); solve [ eauto ]);
    descend'; step hints; eauto.

  Ltac t := solve [ enterFunction
              || (post; evaluate hints; descend; try unifyLocals; repeat (step hints; descend'); eauto;
                  try tree_cong) ].


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
