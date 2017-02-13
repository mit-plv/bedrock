Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc.
Require Import Bedrock.Platform.Facade.examples.WSTuple Bedrock.Platform.Facade.examples.WsTupleList Bedrock.Platform.Facade.examples.WsTuples0 Bedrock.Platform.Facade.examples.ByteString.
Require Import Bedrock.Platform.Facade.examples.QsADTs Bedrock.Platform.Facade.examples.TuplesF.

Inductive skel :=
| Leaf
| Node (sks : list skel).

Definition keepEq (ts : WSTuplSet) (key : W) (bs : list B) : WSTuplSet :=
  fun tup => Ensembles.In _ ts tup /\ exists cap,
              List.nth_error (indexedElement tup) (wordToNat key) = Some (WSBytes cap bs).
Definition keepPosnEq (ts : WSTuplSet) (key : W) (posn : nat) (ch : B) : WSTuplSet :=
  fun tup => Ensembles.In _ ts tup /\ exists cap bs,
              List.nth_error (indexedElement tup) (wordToNat key) = Some (WSBytes cap bs)
              /\ List.nth_error bs posn = Some ch.
Definition keepPosnNe (ts : WSTuplSet) (key : W) (posn : nat) (ch : B) : WSTuplSet :=
  fun tup => Ensembles.In _ ts tup /\ exists cap bs,
              List.nth_error (indexedElement tup) (wordToNat key) = Some (WSBytes cap bs)
              /\ List.nth_error bs posn <> Some ch.
Definition keepLen (ts : WSTuplSet) (key : W) (len : nat) : WSTuplSet :=
  fun tup => Ensembles.In _ ts tup /\ exists cap bs,
              List.nth_error (indexedElement tup) (wordToNat key) = Some (WSBytes cap bs)
              /\ length bs = len.
Definition empty (ts : WSTuplSet) := forall t, ~Ensembles.In _ ts t.


Module Type ADT.
  Parameter trie : W -> W -> WSTuplSet -> W -> HProp.
  Parameter trie' : W -> W -> skel -> WSTuplSet -> nat -> W -> HProp.
  Parameter tries : W -> W -> list skel -> WSTuplSet -> nat -> W -> HProp.

  Axiom trie_fwd : forall len key ts p,
      trie len key ts p ===> Ex tp, Ex sk, (p ==*> len, key, tp) * trie' len key sk ts 0 tp.
  Axiom trie_bwd : forall len key ts p,
      (Ex tp, Ex sk, (p ==*> len, key, tp) * trie' len key sk ts 0 tp) ===> trie len key ts p.

  Axiom trie'_leaf_fwd : forall len key sk ts posn (p : W),
      p = 0
      -> trie' len key sk ts posn p ===> [| sk = Leaf |] * [| empty ts |].
  Axiom trie'_leaf_bwd : forall len key sk ts posn (p : W),
      p = 0
      -> [| sk = Leaf |] * [| empty ts |] ===> trie' len key sk ts posn p.
  Axiom trie'_node_fwd : forall len key sk ts posn (p : W),
      p <> 0
      -> trie' len key sk ts posn p ===>
         Ex sks, Ex mp, Ex tsp,
           [| sk = Node sks |]
           * (p ==*> mp, tsp)
           * wstuples0 len (keepLen ts key posn) mp
           * tries len key sks ts posn tsp.
  Axiom trie'_node_bwd : forall len key sk ts posn (p : W),
      p <> 0
      -> (Ex sks, Ex mp, Ex tsp,
           [| sk = Node sks |]
           * (p ==*> mp, tsp)
           * wstuples0 len (keepLen ts key posn) mp
           * tries len key sks ts posn tsp) ===> trie' len key sk ts posn p.

  Axiom tries_nil_fwd : forall len key sks ts posn (p : W),
      p = 0
      -> tries len key sks ts posn p ===> [| sks = nil |] * [| empty ts |].
  Axiom tries_nil_bwd : forall len key sks ts posn (p : W),
      p = 0
      -> [| sks = nil |] * [| empty ts |] ===> tries len key sks ts posn p.
  Axiom tries_cons_fwd : forall len key sks ts posn (p : W),
      p <> 0
      -> tries len key sks ts posn p ===>
         Ex sk, Ex sks', Ex ch, Ex tp, Ex next,
           [| sks = sk :: sks' |]
           * (p ==*> ch, tp, next)
           * trie' len key sk (keepPosnEq ts key posn (WtoB ch)) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn (WtoB ch)) posn next.
  Axiom tries_cons_bwd : forall len key sks ts posn (p : W),
      p <> 0
      -> (Ex sk, Ex sks', Ex ch, Ex tp, Ex next,
           [| sks = sk :: sks' |]
           * (p ==*> ch, tp, next)
           * trie' len key sk (keepPosnEq ts key posn (WtoB ch)) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn (WtoB ch)) posn next)
         ===> tries len key sks ts posn p.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Section tries.
    Variable trie' : skel -> WSTuplSet -> W -> HProp.
    Variable key : W.
    Variable posn : nat.

    Fixpoint tries' (sks : list skel) (ts : WSTuplSet) (p : W) : HProp :=
      match sks with
      | nil => [| p = 0 |] * [| empty ts |]
      | sk :: sks' => [| p <> 0 |]
                      * Ex ch, Ex tp, Ex next,
                        (p ==*> ch, tp, next)
                        * trie' sk (keepPosnEq ts key posn (WtoB ch)) tp
                        * tries' sks' (keepPosnNe ts key posn (WtoB ch)) next
      end.
  End tries.

  Fixpoint trie' (len key : W) (sk : skel) (ts : WSTuplSet) (posn : nat) (p : W) : HProp :=
    match sk with
    | Leaf => [| p = 0 |] * [| empty ts |]
    | Node sks => [| p <> 0 |]
      * Ex mp, Ex tsp, (p ==*> mp, tsp)
        * wstuples0 len (keepLen ts key posn) mp
        * tries' (fun sk ts p => trie' len key sk ts (S posn) p) key posn sks ts tsp
    end.

  Definition tries (len key : W) (sks : list skel) (ts : WSTuplSet) (posn : nat) (p : W) :=
    tries' (fun sk ts p => trie' len key sk ts (S posn) p) key posn sks ts p.

  Definition trie'' (len key : W) (sk : skel) (ts : WSTuplSet) (posn : nat) (p : W) : HProp :=
    match sk with
    | Leaf => [| p = 0 |] * [| empty ts |]
    | Node sks => [| p <> 0 |]
      * Ex mp, Ex tsp, (p ==*> mp, tsp)
        * wstuples0 len (keepLen ts key posn) mp
        * tries len key sks ts posn tsp
    end.

  Theorem trie'_trie'' : forall len key sk ts posn p,
      trie' len key sk ts posn p = trie'' len key sk ts posn p.
  Proof.
    destruct sk; simpl; intuition.
  Qed.

  Definition trie (len key : W) (ts : WSTuplSet) (p : W) : HProp :=
    Ex tp, Ex sk, (p ==*> len, key, tp) * trie' len key sk ts 0 tp.

  Theorem trie_fwd : forall len key ts p,
      trie len key ts p ===> Ex tp, Ex sk, (p ==*> len, key, tp) * trie' len key sk ts 0 tp.
  Proof.
    unfold trie; sepLemma.
  Qed.

  Theorem trie_bwd : forall len key ts p,
      (Ex tp, Ex sk, (p ==*> len, key, tp) * trie' len key sk ts 0 tp) ===> trie len key ts p.
  Proof.
    unfold trie; sepLemma.
  Qed.

  Theorem trie'_leaf_fwd : forall len key sk ts posn (p : W),
      p = 0
      -> trie' len key sk ts posn p ===> [| sk = Leaf |] * [| empty ts |].
  Proof.
    intros; rewrite trie'_trie''; destruct sk; sepLemma.
  Qed.

  Theorem trie'_leaf_bwd : forall len key sk ts posn (p : W),
      p = 0
      -> [| sk = Leaf |] * [| empty ts |] ===> trie' len key sk ts posn p.
  Proof.
    intros; rewrite trie'_trie''; repeat sepLemma.
  Qed.

  Theorem trie'_node_fwd : forall len key sk ts posn (p : W),
      p <> 0
      -> trie' len key sk ts posn p ===>
         Ex sks, Ex mp, Ex tsp,
           [| sk = Node sks |]
           * (p ==*> mp, tsp)
           * wstuples0 len (keepLen ts key posn) mp
           * tries len key sks ts posn tsp.
  Proof.
    intros; rewrite trie'_trie''; destruct sk; sepLemma.
  Qed.

  Theorem trie'_node_bwd : forall len key sk ts posn (p : W),
      p <> 0
      -> (Ex sks, Ex mp, Ex tsp,
           [| sk = Node sks |]
           * (p ==*> mp, tsp)
           * wstuples0 len (keepLen ts key posn) mp
           * tries len key sks ts posn tsp) ===> trie' len key sk ts posn p.
  Proof.
    intros; rewrite trie'_trie''; repeat sepLemma.
  Qed.

  Theorem tries_nil_fwd : forall len key sks ts posn (p : W),
      p = 0
      -> tries len key sks ts posn p ===> [| sks = nil |] * [| empty ts |].
  Proof.
    destruct sks; sepLemma.
  Qed.

  Theorem tries_nil_bwd : forall len key sks ts posn (p : W),
      p = 0
      -> [| sks = nil |] * [| empty ts |] ===> tries len key sks ts posn p.
  Proof.
    repeat sepLemma.
  Qed.

  Theorem tries_cons_fwd : forall len key sks ts posn (p : W),
      p <> 0
      -> tries len key sks ts posn p ===>
         Ex sk, Ex sks', Ex ch, Ex tp, Ex next,
           [| sks = sk :: sks' |]
           * (p ==*> ch, tp, next)
           * trie' len key sk (keepPosnEq ts key posn (WtoB ch)) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn (WtoB ch)) posn next.
  Proof.
    destruct sks; sepLemma.
  Qed.

  Theorem tries_cons_bwd : forall len key sks ts posn (p : W),
      p <> 0
      -> (Ex sk, Ex sks', Ex ch, Ex tp, Ex next,
           [| sks = sk :: sks' |]
           * (p ==*> ch, tp, next)
           * trie' len key sk (keepPosnEq ts key posn (WtoB ch)) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn (WtoB ch)) posn next)
         ===> tries len key sks ts posn p.
  Proof.
    repeat sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (trie_fwd, trie'_leaf_fwd, trie'_node_fwd, tries_nil_fwd, tries_cons_fwd)
          (trie_bwd, trie'_leaf_bwd, trie'_node_bwd, tries_nil_bwd, tries_cons_bwd).
Defined.

Definition newS := SPEC("extra_stack", "len", "key") reserving 7
  PRE[V] [| V "len" >= $2 |] * [| V "key" < V "len" |] * mallocHeap 0
  POST[R] trie (V "len") (V "key") Empty R * mallocHeap 0.

Definition insertS := SPEC("extra_stack", "self", "tup") reserving 21
  Al len, Al key, Al ts, Al t, Al ts',
  PRE[V] trie len key ts (V "self") * wstuple t (V "tup") * mallocHeap 0
    * [| length t = wordToNat len |]
    * [| exists cap bs, List.nth_error t (wordToNat len) = Some (WSBytes cap bs) |]
    * [| insert ts t ts' |]
  POST[R] [| R = $0 |] * trie len key ts' (V "self") * mallocHeap 0.

Definition findS := SPEC("extra_stack", "self", "k") reserving 34
  Al len, Al key, Al ts, Al cap, Al bs,
  PRE[V] trie len key ts (V "self") * bytes cap bs (V "k") * mallocHeap 0
  POST[R] trie len key ts (V "self") * Ex ls, wlseq ls R
        * bytes cap bs (V "k") * mallocHeap 0
        * [| EnsembleIndexedListEquivalence (keepEq ts key bs) ls |].

Definition enumerateS := SPEC("extra_stack", "self") reserving 34
  Al len, Al key, Al ts,
  PRE[V] trie len key ts (V "self") * [| functional ts |] * mallocHeap 0
  POST[R] trie len key ts (V "self") * Ex ls, wlseq ls R * mallocHeap 0
          * [| EnsembleIndexedListEquivalence ts ls |].


Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "WSTuple"!"get" @ [WSTuple.getS],
                           "WsTuples0"!"new" @ [WsTuples0.newS], "WsTuples0"!"insert" @ [WsTuples0.insertS],
                           "WsTuples0"!"enumerateInto" @ [WsTuples0.enumerateIntoS] ]]
  bmodule "Trie" {{
    bfunction "new"("extra_stack", "len", "key") [newS]
      "extra_stack" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
              * [| (V "len" >= $2)%word |] * [| (V "key" < V "len")%word |]
       POST[R'] trie (V "len") (V "key") Empty R'];;

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

Ltac t := sep_auto; eauto.

Theorem ok : moduleOk m.
Proof.
  vcgen.

  t.
  t.
  t.
  t.
  t.

  vcgen; try abstract t; t.

  Grab Existential Variables.
  exact 0.
Qed.
