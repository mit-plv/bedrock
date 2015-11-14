Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.TuplesF.


Section tuples0.
  Open Scope Sep_scope.

  Definition tuples0 (len : nat) (ts : tuples) (p : W) :=
    Ex ls, Ex lsp, (p ==*> natToW len, lsp) * lseq ls lsp * [| EnsembleIndexedListEquivalence ts ls |]
      * [| $2 <= natToW len |]
      * [| forall t, IndexedEnsemble_In ts t -> length t = len |].
End tuples0.

Definition Empty : tuples := fun _ => False.

Definition newS := SPEC("extra_stack", "len") reserving 11
  PRE[V] [| V "len" >= $2 |] * mallocHeap 0
  POST[R] tuples0 (wordToNat (V "len")) Empty R * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "TupleList"!"new" @ [TupleListF.newS] ]]
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

Theorem ok : moduleOk m.
Proof.
  vcgen.

  Ltac t := unfold tuples0; sep_auto; eauto.

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
