Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.MoreArrays.


Module Type ADT.
  Parameter tuple : list W -> W -> HProp.

  Axiom tuple_fwd : forall ls c, tuple ls c ===> [| c <> 0 |] * [| freeable c (length ls) |] * array ls c.
  Axiom tuple_bwd : forall ls (c : W), [| c <> 0 |] * [| freeable c (length ls) |] * array ls c ===> tuple ls c.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Definition tuple (ls : list W) (c : W) : HProp := [| c <> 0 |] * [| freeable c (length ls) |] * array ls c.

  Theorem tuple_fwd : forall ls c, tuple ls c ===> [| c <> 0 |] * [| freeable c (length ls) |] * array ls c.
  Proof.
    unfold tuple; sepLemma.
  Qed.

  Theorem tuple_bwd : forall ls (c : W), [| c <> 0 |] * [| freeable c (length ls) |] * array ls c ===> tuple ls c.
  Proof.
    unfold tuple; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (tuple_fwd, allocate_array) (tuple_bwd, free_array).
Defined.

Definition newS := newS tuple 8.
Definition deleteS := deleteS tuple 7.
Definition getS := getS tuple 8.
Definition setS := setS tuple 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ListSeq" {{
    bfunction "new"("extra_stack", "len", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, "len")
      [PRE[V, R] R =?> wordToNat (V "len") * [| R <> 0 |] * [| freeable R (wordToNat (V "len")) |] * mallocHeap 0
       POST[R'] Ex ls, tuple ls R' * [| length ls = wordToNat (V "len") |] * mallocHeap 0];;

      Note [make_array];;
      Return "x"
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

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
  t.
Qed.
