Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.TuplesF.


Section tuples0.
  Open Scope Sep_scope.

  Definition tuples0 (len : nat) (ts : tuples) (p : W) :=
    Ex ls, Ex lsp, Ex bound, (p ==*> natToW len, lsp) * lseq ls lsp * [| EnsembleIndexedListEquivalence ts ls |]
      * [| $2 <= natToW len |]
      * [| forall t, IndexedEnsemble_In ts t -> length t = len |]
      * [| UnConstrFreshIdx ts bound |].
End tuples0.

Definition Empty : tuples := fun _ => False.

Definition newS := SPEC("extra_stack", "len") reserving 11
  PRE[V] [| V "len" >= $2 |] * mallocHeap 0
  POST[R] tuples0 (wordToNat (V "len")) Empty R * mallocHeap 0.

Definition pushS := SPEC("extra_stack", "self", "tup") reserving 12
  Al len, Al ts, Al t,
  PRE[V] tuples0 len ts (V "self") * tuple t (V "tup") * [| length t = len |] * mallocHeap 0
  POST[R] [| R = $0 |] * Ex ts', [| insert ts t ts' |] * tuples0 len ts' (V "self") * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "TupleList"!"new" @ [TupleListF.newS], "TupleList"!"push" @ [TupleListF.pushS] ]]
  bmodule "Tuples0" {{
    bfunction "new"("extra_stack", "len", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0 * [| (V "len" >= $2)%word |]
       POST[R'] tuples0 (wordToNat (V "len")) Empty R' * mallocHeap 0];;

      "extra_stack" <-- Call "TupleList"!"new"("extra_stack")
      [PRE[V, R] V "x" =?> 2 * [| V "x" <> 0 |] * [| freeable (V "x") 2 |] * mallocHeap 0 * [| (V "len" >= $2)%word |]
         * lseq nil R
       POST[R'] tuples0 (wordToNat (V "len")) Empty R' * mallocHeap 0];;

      "x" *<- "len";;
      "x" + 4 *<- "extra_stack";;
      Return "x"
    end

    with bfunction "push"("extra_stack", "self", "tup") [pushS]
      "self" <-* "self" + 4;;
      "self" <-- Call "TupleList"!"push"("extra_stack", "self", "tup")
      [PRE[_] Emp
       POST[R] [| R = $0 |] ];;

      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Local Hint Constructors NoDup.

Lemma Empty_nil : EnsembleIndexedListEquivalence Empty nil.
Proof.
  hnf; intuition.
  exists 0.
  hnf; destruct 1.
  hnf.
  exists nil.
  simpl; intuition.
Qed.

Hint Resolve Empty_nil.

Lemma natToW_wordToNat : forall w : W,
  natToW (wordToNat w) = w.
Proof.
  intros; apply natToWord_wordToNat.
Qed.

Hint Rewrite natToW_wordToNat : sepFormula.

Hint Extern 1 (_ = wordToNat _) =>
  match goal with
  | [ H : IndexedEnsemble_In Empty _ |- _] => destruct H as [ ? [ ] ]
  end.

Lemma fresh_Empty : UnConstrFreshIdx Empty O.
Proof.
  hnf; destruct 1.
Qed.

Hint Resolve fresh_Empty.

Definition insertAt (ts : tuples) (idx : nat) (t : tupl) : tuples :=
  EnsembleInsert {| elementIndex := idx;
                    indexedElement:= t |} ts.

Theorem insert_insertAt : forall ts idx t,
  UnConstrFreshIdx ts idx
  -> insert ts t (insertAt ts idx t).
Proof.
  unfold insert, insertAt, UnConstrFreshIdx, Ensembles.In; simpl; intros.
  exists idx; intuition subst.
  apply H in H0; omega.
Qed.

Hint Immediate insert_insertAt.

Theorem EnsembleIndexedListEquivalence_insertAt : forall ts idx t ls,
  UnConstrFreshIdx ts idx
  -> EnsembleIndexedListEquivalence ts ls
  -> EnsembleIndexedListEquivalence (insertAt ts idx t) (t :: ls).
Proof.
  unfold insertAt, EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence, UnConstrFreshIdx, EnsembleInsert, Ensembles.In; simpl; firstorder idtac.
  exists (S idx); intuition subst; simpl; intuition.
  exists ({| elementIndex := idx; indexedElement := t |} :: x0); simpl; intuition.
  firstorder idtac.
  firstorder idtac.
  constructor; auto.
  intro.
  apply in_map_iff in H4; destruct H4; intuition subst.
  apply H2 in H6.
  apply H in H6.
  omega.
Qed.

Hint Immediate EnsembleIndexedListEquivalence_insertAt.

Theorem bounded_insertAt : forall ts idx t t',
  (forall t'', IndexedEnsemble_In ts t'' -> length t'' = length t)
  -> IndexedEnsemble_In (insertAt ts idx t) t'
  -> length t' = length t.
Proof.
  unfold insertAt, IndexedEnsemble_In, EnsembleInsert, Ensembles.In; simpl; firstorder congruence.
Qed.

Hint Immediate bounded_insertAt.

Theorem fresh_insertAt : forall ts idx t,
  UnConstrFreshIdx ts idx
  -> UnConstrFreshIdx (insertAt ts idx t) (S idx).
Proof.
  unfold insertAt, UnConstrFreshIdx, EnsembleInsert, Ensembles.In; simpl; firstorder idtac.
  subst; simpl; omega.
  firstorder omega.
Qed.

Hint Immediate fresh_insertAt.

Theorem ok : moduleOk m.
Proof.
  vcgen.

  Ltac t := solve [ unfold tuples0; sep_auto; eauto ].

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
