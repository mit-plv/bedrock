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

Definition agreeUpto (key : nat) (ts : WSTuplSet) (posn : nat) (bs : list B) :=
  forall i, (i < posn)%nat
    -> forall t, ts t
      -> exists cap bs', nth_error (indexedElement t) key = Some (WSBytes cap bs')
                         /\ nth_error bs i = nth_error bs' i.


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
           * (p ==*> BtoW ch, tp, next) * [| tp <> 0 |]
           * trie' len key sk (keepPosnEq ts key posn ch) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn ch) posn next.
  Axiom tries_cons_bwd : forall len key sks ts posn (p : W),
      p <> 0
      -> (Ex sk, Ex sks', Ex ch, Ex tp, Ex next,
           [| sks = sk :: sks' |]
           * (p ==*> BtoW ch, tp, next) * [| tp <> 0 |]
           * trie' len key sk (keepPosnEq ts key posn ch) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn ch) posn next)
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
                        (p ==*> BtoW ch, tp, next) * [| tp <> 0 |]
                        * trie' sk (keepPosnEq ts key posn ch) tp
                        * tries' sks' (keepPosnNe ts key posn ch) next
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
           * (p ==*> BtoW ch, tp, next) * [| tp <> 0 |]
           * trie' len key sk (keepPosnEq ts key posn ch) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn ch) posn next.
  Proof.
    destruct sks; sepLemma.
  Qed.

  Theorem tries_cons_bwd : forall len key sks ts posn (p : W),
      p <> 0
      -> (Ex sk, Ex sks', Ex ch, Ex tp, Ex next,
           [| sks = sk :: sks' |]
           * (p ==*> BtoW ch, tp, next) * [| tp <> 0 |]
           * trie' len key sk (keepPosnEq ts key posn ch) (S posn) tp
           * tries len key sks' (keepPosnNe ts key posn ch) posn next)
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

Definition findS := SPEC("extra_stack", "self", "k", "len") reserving 39
  Al len, Al key, Al ts, Al cap, Al bs,
  PRE[V] trie len key ts (V "self") * bytes cap bs (V "k") * mallocHeap 0
         * [| wordToNat (V "len") = length bs |]
  POST[R] trie len key ts (V "self") * Ex ls, wlseq ls R
        * bytes cap bs (V "k") * mallocHeap 0
        * [| EnsembleIndexedListEquivalence (keepEq ts key bs) ls |].

Definition enumerateS := SPEC("extra_stack", "self") reserving 34
  Al len, Al key, Al ts,
  PRE[V] trie len key ts (V "self") * [| functional ts |] * mallocHeap 0
  POST[R] trie len key ts (V "self") * Ex ls, wlseq ls R * mallocHeap 0
          * [| EnsembleIndexedListEquivalence ts ls |].

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "WSTuple"!"get" @ [WSTuple.getS], "ByteString"!"get" @ [ByteString.getS],
                           "WsTupleList"!"new" @ [WsTupleList.newS],
                           "WsTuples0"!"new" @ [WsTuples0.newS], "WsTuples0"!"insert" @ [WsTuples0.insertS],
                           "WsTuples0"!"enumerate" @ [WsTuples0.enumerateS],
                           "WsTuples0"!"enumerateInto" @ [WsTuples0.enumerateIntoS] ]]
  bmodule "Trie" {{
    bfunction "new"("extra_stack", "len", "key") [newS]
      "extra_stack" <-- Call "malloc"!"malloc"(0, 3)
      [PRE[V, R] R =?> 3 * [| R <> 0 |] * [| freeable R 3 |]
              * [| (V "len" >= $2)%word |] * [| (V "key" < V "len")%word |]
       POST[R'] trie (V "len") (V "key") Empty R'];;

      "extra_stack" *<- "len";;
      "extra_stack" + 4 *<- "key";;
      "extra_stack" + 8 *<- 0;;
      Return "extra_stack"
    end

    with bfunction "find"("extra_stack", "self", "k", "len", "key", "posn", "ch", "ch2", "stop") [findS]
      "key" <-* "self" + 4;;
      "self" <-* "self" + 8;;
      "posn" <- 0;;

      [Al len, Al key, Al ts, Al cap, Al bs, Al sk,
       PRE[V] trie' len key sk ts (wordToNat (V "posn")) (V "self") * bytes cap bs (V "k") * mallocHeap 0
         * [| wordToNat (V "len") = length bs |] * [| V "posn" <= V "len" |]%word
         * [| agreeUpto (wordToNat key) ts (wordToNat (V "posn")) bs |]
       POST[R] trie' len key sk ts (wordToNat (V "posn")) (V "self") * Ex ls, wlseq ls R
         * bytes cap bs (V "k") * mallocHeap 0
         * [| EnsembleIndexedListEquivalence (keepEq ts key bs) ls |]]
      While ("self" <> 0) {
        If ("posn" = "len") {
          (* We've consumed all characters in the key, so it's now or never.
           * We need to return whatever is associated with this node. *)
          "self" <-* "self";;
          "self" <-- Call "WsTuples0"!"enumerate"("extra_stack", "self")
          [PRE[_, R] Emp
           POST[R'] [| R' = R |] ];;
          Return "self"
        } else {
          (* In the list of possible next characters, find the one that matches
           * this position in the key. *)
          "ch" <-- Call "ByteString"!"get"("extra_stack", "k", "posn")
          [Al len, Al key, Al ts, Al cap, Al bs, Al sk,
           PRE[V, R] trie' len key sk ts (wordToNat (V "posn")) (V "self") * bytes cap bs (V "k") * mallocHeap 0
             * [| wordToNat (V "len") = length bs |] * [| V "posn" < V "len" |]%word
             * [| V "self" <> 0 |] * [| R = BtoW (nth (wordToNat (V "posn")) bs (wzero _)) |]
             * [| agreeUpto (wordToNat key) ts (wordToNat (V "posn")) bs |]

           POST[R'] trie' len key sk ts (wordToNat (V "posn")) (V "self") * Ex ls, wlseq ls R'
             * bytes cap bs (V "k") * mallocHeap 0
             * [| EnsembleIndexedListEquivalence (keepEq ts key bs) ls |]];;

          "self" <-* "self" + 4;;
          "stop" <- 0;;
          [Al len, Al key, Al ts, Al cap, Al bs, Al sks,
           PRE[V] bytes cap bs (V "k") * mallocHeap 0
             * tries len key sks ts (wordToNat (V "posn")) (V "self")
             * [| wordToNat (V "len") = length bs |] * [| V "posn" < V "len" |]%word
             * [| V "ch" = BtoW (nth (wordToNat (V "posn")) bs (wzero _)) |]
             * [| agreeUpto (wordToNat key) ts (wordToNat (V "posn")) bs |]
           POST[R] Ex ls, wlseq ls R
             * bytes cap bs (V "k") * mallocHeap 0
             * tries len key sks ts (wordToNat (V "posn")) (V "self")
             * [| EnsembleIndexedListEquivalence (keepEq ts key bs) ls |]]
          While ("stop" = 0) {
            If ("self" = 0) {
              "stop" <- 1
            } else {
              "ch2" <-* "self";;
              If ("ch" = "ch2") {
                (* Found a match! *)
                "stop" <- 1
              } else {
                "self" <-* "self" + 8
              }
            }
          };;

          If ("self" = 0) {
            (* No match for the next character, so we give up. *)
            "self" <-- Call "WsTupleList"!"new"("extra_stack")
            [PRE[_, R] Emp
             POST[R'] [| R' = R |] ];;
            Return "self"
          } else {
            "ch2" <-* "self";;
            If ("ch" = "ch2") {
              (* Reconfirmed the match.
               * (The code is structured this way to make the proof easier.) *)
              "self" <-* "self" + 4;;
              "posn" <- 1 + "posn"
            } else {
              Diverge (* Should be impossible, but we aren't proving it now. *)
            }
          }
        }
      };;

      "self" <-- Call "WsTupleList"!"new"("extra_stack")
      [PRE[_, R] Emp
      POST[R'] [| R' = R |] ];;
      Return "self"
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma empty_Empty : empty Empty.
Proof.
  hnf; intuition.
Qed.

Hint Resolve empty_Empty.

Lemma agreeUpto_zero : forall key ts bs,
    agreeUpto key ts 0 bs.
Proof.
  unfold agreeUpto; intuition.
Qed.

Local Hint Immediate agreeUpto_zero.

Lemma increment : forall posn : W,
    (exists len, posn < len)
    -> wordToNat (natToW 1 ^+ posn) = S (wordToNat posn).
Proof.
  firstorder.
  rewrite wplus_comm.
  erewrite <- next.
  omega.
  eassumption.
Qed.

Hint Rewrite increment using (eexists; eassumption) : sepFormula.

Lemma oneplus_bound : forall posn len,
    posn < len
    -> natToW 1 ^+ posn <= len.
Proof.
  intros.
  pre_nomega.
  rewrite wplus_comm.
  erewrite <- next.
  omega.
  pre_nomega.
  eassumption.
Qed.

Local Hint Immediate oneplus_bound.

Lemma nth_error_nth : forall A (d : A) n ls,
    (n < length ls)%nat
    -> nth_error ls n = Some (nth n ls d).
Proof.
  induction n; destruct ls; simpl; intuition.
Qed.

Lemma agreeUpto_keepPosnEq : forall key ts (posn : W) ch ch' bs len,
    agreeUpto (wordToNat key) ts (wordToNat posn) bs
    -> ch' = BtoW ch
    -> ch' = BtoW (nth (wordToNat posn) bs (wzero 8))
    -> posn < len
    -> wordToNat len = length bs
    -> agreeUpto (wordToNat key) (keepPosnEq ts key (wordToNat posn) ch) (S (wordToNat posn)) bs.
Proof.
  unfold agreeUpto, keepPosnEq; intuition.
  destruct H7 as [ ? [ ] ]; intuition.
  do 2 eexists; split; eauto.
  Require Import Arith.
  destruct (eq_nat_dec i (wordToNat posn)); subst.

  apply (f_equal WtoB) in H1.
  repeat erewrite BtoW_WtoB in H1 by reflexivity.
  subst.
  erewrite nth_error_nth.
  eauto.
  nomega.

  eapply H in H6.
  destruct H6 as [ ? [ ? [ ] ] ].
  rewrite H7 in H0.
  inversion_clear H0.
  eassumption.
  omega.
Qed.

Local Hint Immediate agreeUpto_keepPosnEq.

Lemma EnsembleIndexedListEquivalence_cong : forall A (ts ts' : @IndexedEnsemble A) ls,
    EnsembleIndexedListEquivalence ts ls
    -> (forall x, ts x <-> ts' x)
    -> EnsembleIndexedListEquivalence ts' ls.
Proof.
  unfold EnsembleIndexedListEquivalence.
  firstorder.
Qed.

Lemma keepEq_keepPosnEq : forall ts ch ch' (posn len : W) ls key bs,
    EnsembleIndexedListEquivalence
      (keepEq (keepPosnEq ts key (wordToNat posn) ch') key bs) ls
    -> ch = BtoW ch'
    -> ch = BtoW (nth (wordToNat posn) bs (wzero 8))
    -> wordToNat len = length bs
    -> posn < len
    -> EnsembleIndexedListEquivalence (keepEq ts key bs) ls.
Proof.
  intros.
  eapply EnsembleIndexedListEquivalence_cong.
  eassumption.
  unfold keepEq, keepPosnEq, Ensembles.In; subst; intuition.
  destruct H5.
  do 2 eexists; split; eauto.
  apply (f_equal WtoB) in H1.
  erewrite BtoW_WtoB in H1 by reflexivity.
  subst.
  erewrite nth_error_nth.
  f_equal.
  erewrite BtoW_WtoB by reflexivity.
  eauto.
  pre_nomega.
  rewrite H2 in H3.
  assumption.
Qed.

Local Hint Immediate keepEq_keepPosnEq.

Lemma agreeUpto_equal' : forall (bs1 bs2 : list B),
    (forall i, (i < length bs1)%nat
               -> nth_error bs1 i = nth_error bs2 i)
    -> length bs1 = length bs2
    -> bs1 = bs2.
Proof.
  induction bs1; destruct bs2; simpl; intuition.
  assert (0 < S (length bs1))%nat by omega.
  generalize (H 0); simpl; intuition.
  inversion_clear H3.
  f_equal.
  apply IHbs1; intuition.
  apply (H (S i)); auto.
Qed.

Lemma agreeUpto_equal : forall key ts t bs1 bs2 cap,
    agreeUpto key ts (length bs1) bs1
    -> length bs1 = length bs2
    -> ts t
    -> nth_error (indexedElement t) key = Some (WSBytes cap bs2)
    -> bs1 = bs2.
Proof.
  unfold agreeUpto; intros.
  eapply agreeUpto_equal'.
  intros.
  eapply H in H3; try eassumption.
  destruct H3 as [ ? [ ] ]; intuition.
  rewrite H2 in H4; inversion_clear H4.
  assumption.
  assumption.
Qed.

Lemma keepLen_keepEq : forall ts (posn len : W) ls key bs,
    EnsembleIndexedListEquivalence (keepLen ts key (wordToNat posn)) ls
    -> posn = len
    -> wordToNat len = length bs
    -> agreeUpto (wordToNat key) ts (wordToNat posn) bs
    -> EnsembleIndexedListEquivalence (keepEq ts key bs) ls.
Proof.
  intros.
  eapply EnsembleIndexedListEquivalence_cong.
  eassumption.
  unfold keepEq, keepLen, Ensembles.In; subst; intuition.

  destruct H4 as [ ? [ ] ]; intuition.
  replace x1 with bs in H4.
  eauto.
  eapply agreeUpto_equal; eauto.
  rewrite <- H1.
  assumption.

  firstorder.
Qed.

Local Hint Immediate keepLen_keepEq.

Lemma length_bound : forall (posn : W) len len',
    posn <> len'
    -> posn <= len'
    -> wordToNat len' = len
    -> (wordToNat posn < len)%nat.
Proof.
  intros; subst.
  pre_nomega.
  apply Bootstrap.wordToNat_ninj in H.
  omega.
Qed.

Local Hint Immediate length_bound.

Lemma length_bound' : forall (posn : W) len,
    posn <> len
    -> posn <= len
    -> posn < len.
Proof.
  intros; subst.
  pre_nomega.
  apply Bootstrap.wordToNat_ninj in H.
  omega.
Qed.

Local Hint Immediate length_bound'.

Lemma agreeUpto_keepPosnNe : forall key ts (posn : W) ch ch' bs len,
    agreeUpto (wordToNat key) ts (wordToNat posn) bs
    -> ch = BtoW (nth (wordToNat posn) bs (wzero _))
    -> ch <> BtoW ch'
    -> posn < len
    -> wordToNat len = length bs
    -> agreeUpto (wordToNat key) (keepPosnNe ts key (wordToNat posn) ch') (wordToNat posn) bs.
Proof.
  unfold agreeUpto, keepPosnNe; intuition.
Qed.

Local Hint Immediate agreeUpto_keepPosnNe.

Lemma keepEq_keepPosnNe : forall ts ch ch' (posn len : W) ls key bs,
    EnsembleIndexedListEquivalence
      (keepEq (keepPosnNe ts key (wordToNat posn) ch') key bs) ls
    -> ch = BtoW (nth (wordToNat posn) bs (wzero 8))
    -> ch <> BtoW ch'
    -> wordToNat len = length bs
    -> posn < len
    -> EnsembleIndexedListEquivalence (keepEq ts key bs) ls.
Proof.
  intros.
  eapply EnsembleIndexedListEquivalence_cong.
  eassumption.
  unfold keepEq, keepPosnNe, Ensembles.In; subst; intuition.
  destruct H5.
  do 2 eexists; split; eauto.
  intro.
  erewrite nth_error_nth in H5.
  inversion H5; clear H5.
  apply H1.
  apply (f_equal BtoW) in H7.
  eauto.
  pre_nomega.
  rewrite H2 in H3.
  assumption.
Qed.

Local Hint Immediate keepEq_keepPosnNe.

Lemma keepEq_empty : forall ts key bs,
    empty ts
    -> EnsembleIndexedListEquivalence (keepEq ts key bs) nil.
Proof.
  unfold EnsembleIndexedListEquivalence, UnConstrFreshIdx, UnIndexedEnsembleListEquivalence, keepEq, Ensembles.In.
  firstorder.
  exact 0.
  exists nil; simpl; firstorder.
  constructor.
Qed.

Local Hint Immediate keepEq_empty.

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

Ltac t := solve [ enterFunction
                  || (post; evaluate hints; try evaluate hints; descend; try unifyLocals;
                      repeat (step hints; descend); eauto; cbv beta; congruence) ].

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
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  Grab Existential Variables.
  exact 0.
Qed.
