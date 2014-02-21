Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Inv.
  Module Import InvMake := Make E.
  Import Semantics.
  Import SemanticsMake.

  Lemma make_triples_Word : forall pairs outs, length outs = length pairs -> map (@Word _) (make_triples pairs outs) = map fst pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_Word_ADTIn : forall pairs outs, length outs = length pairs -> map (fun x => (Word x, ADTIn x)) (make_triples pairs outs) = pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_ADTIn : forall pairs outs, length outs = length pairs -> map (@ADTIn _) (make_triples pairs outs) = map snd pairs.
    induction pairs; destruct outs; simpl; intuition.
    f_equal; auto.
  Qed.

  Lemma make_triples_length : forall pairs outs, length outs = length pairs -> length (make_triples pairs outs) = length pairs.
    induction pairs; destruct outs; simpl; intuition.
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