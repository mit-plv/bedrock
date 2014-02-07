Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Inv.
  Module Import InvMake := Make E.
  Import SafeMake.SemanticsMake.
  Import HeapMake.

  Lemma make_triples_Word : forall pairs outs, length outs = length pairs -> map Word (make_triples pairs outs) = map fst pairs.
    admit.
  Qed.

  Lemma make_triples_Word_ADTIn : forall pairs outs, length outs = length pairs -> map (fun x => (Word x, ADTIn x)) (make_triples pairs outs) = pairs.
    admit.
  Qed.

  Lemma make_triples_ADTIn : forall pairs outs, length outs = length pairs -> map ADTIn (make_triples pairs outs) = map snd pairs.
    admit.
  Qed.

  Lemma make_triples_length : forall pairs outs, length outs = length pairs -> length (make_triples pairs outs) = length pairs.
    admit.
  Qed.

  Lemma heap_merge_store_out : 
    forall h pairs outs, 
      good_inputs h pairs -> 
      let h1 := make_heap pairs in 
      let triples := make_triples pairs outs in
      heap_merge (heap_diff h h1) (fold_left store_out triples h1) = fold_left store_out triples h.
    admit.
  Qed.

End Make.