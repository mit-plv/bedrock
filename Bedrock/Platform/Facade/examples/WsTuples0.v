Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc.
Require Import Bedrock.Platform.Facade.examples.WSTuple Bedrock.Platform.Facade.examples.WsTupleList.
Require Import Bedrock.Platform.Facade.examples.QsADTs Bedrock.Platform.Facade.examples.TuplesF.
Require Import Bedrock.Platform.Facade.examples.Tuples0F.


Section wstuples0.
  Open Scope Sep_scope.

  Definition wstuples0 (len : W) (ts : WSTuplSet) (p : W) :=
    Ex ls, Ex lsp, (p ==*> len, lsp) * wlseq ls lsp * [| EnsembleIndexedListEquivalence ts ls |]
      * [| $2 <= len |]
      * [| forall t, IndexedEnsemble_In ts t -> length t = wordToNat len |].
End wstuples0.

Theorem wstuples0_Equiv : forall len ts1 ts2 p,
  Equiv ts1 ts2
  -> wstuples0 len ts1 p ===> wstuples0 len ts2 p.
Proof.
  unfold wstuples0; sepLemma.
  firstorder idtac.
  firstorder idtac.
Qed.

Definition Empty : WSTuplSet := fun _ => False.

Definition newS := SPEC("extra_stack", "len") reserving 11
  PRE[V] [| V "len" >= $2 |] * mallocHeap 0
  POST[R] wstuples0 (V "len") Empty R * mallocHeap 0.

Definition insertS := SPEC("extra_stack", "self", "tup") reserving 12
  Al len, Al ts, Al t, Al ts',
  PRE[V] wstuples0 len ts (V "self") * wstuple t (V "tup") * [| length t = wordToNat len |] * mallocHeap 0
         * [| insert ts t ts' |]
  POST[R] [| R = $0 |] * wstuples0 len ts' (V "self") * mallocHeap 0.

Definition enumerateS := SPEC("extra_stack", "self") reserving 31
  Al len, Al ts,
  PRE[V] wstuples0 len ts (V "self") * mallocHeap 0
  POST[R] wstuples0 len ts (V "self") * Ex ls, wlseq ls R * [| EnsembleIndexedListEquivalence ts ls |] * mallocHeap 0.

Definition enumerateIntoS := SPEC("extra_stack", "self", "ls") reserving 32
  Al len, Al ts, Al ls,
  PRE[V] wstuples0 len ts (V "self") * wlseq ls (V "ls") * mallocHeap 0
  POST[R] [| R = $0 |] * wstuples0 len ts (V "self") * Ex ls', wlseq (ls' ++ ls) (V "ls") * [| EnsembleIndexedListEquivalence ts ls' |] * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "WsTupleList"!"new" @ [WsTupleList.newS], "WsTupleList"!"push" @ [WsTupleList.pushS],
                           "WsTupleList"!"copy" @ [WsTupleList.copyS], "WsTupleList"!"copyAppend" @ [WsTupleList.copyAppendS] ]]
  bmodule "WsTuples0" {{
    bfunction "new"("extra_stack", "len", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0 * [| (V "len" >= $2)%word |]
       POST[R'] wstuples0 (V "len") Empty R' * mallocHeap 0];;

      "extra_stack" <-- Call "WsTupleList"!"new"("extra_stack")
      [PRE[V, R] V "x" =?> 2 * [| V "x" <> 0 |] * [| freeable (V "x") 2 |] * mallocHeap 0 * [| (V "len" >= $2)%word |]
         * wlseq nil R
       POST[R'] wstuples0 (V "len") Empty R' * mallocHeap 0];;

      "x" *<- "len";;
      "x" + 4 *<- "extra_stack";;
      Return "x"
    end

    with bfunction "insert"("extra_stack", "self", "tup") [insertS]
      "self" <-* "self" + 4;;
      "self" <-- Call "WsTupleList"!"push"("extra_stack", "self", "tup")
      [PRE[_] Emp
       POST[R] [| R = $0 |] ];;

      Return 0
    end

    with bfunction "enumerate"("extra_stack", "self") [enumerateS]
      "extra_stack" <-* "self";;
      "self" <-* "self" + 4;;
      "self" <-- Call "WsTupleList"!"copy"("extra_stack", "self", "extra_stack")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;

      Return "self"
    end

    with bfunction "enumerateInto"("extra_stack", "self", "ls") [enumerateIntoS]
      "extra_stack" <-* "self";;
      "self" <-* "self" + 4;;
      "self" <-- Call "WsTupleList"!"copyAppend"("extra_stack", "self", "ls", "extra_stack")
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

Local Hint Resolve Empty_nil.

Hint Rewrite natToW_wordToNat : sepFormula.

Local Hint Extern 1 (_ = wordToNat _) =>
  match goal with
  | [ H : IndexedEnsemble_In Empty _ |- _] => destruct H as [ ? [ ] ]
  end.

Local Hint Resolve fresh_Empty.

Local Hint Extern 2 (EnsembleIndexedListEquivalence _ (_ :: _)) =>
  eapply EnsembleIndexedListEquivalence_insert; eassumption.

Local Hint Extern 2 (_ _ = _) => fold (@length WS); eapply bounded_insert.

Local Hint Immediate allTuplesLen_setwise.

Theorem ok : moduleOk m.
Proof.
  vcgen; abstract (unfold wstuples0; sep_auto; eauto).
Qed.
