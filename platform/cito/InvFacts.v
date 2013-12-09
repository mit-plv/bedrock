Require Import Inv.
Require Import Semantics.

Set Implicit Arguments.

Lemma make_triples_Word : forall pairs outs, length outs = length pairs -> map Word (make_triples pairs outs) = map fst pairs.
  admit.
Qed.

Lemma make_triples_Forall_pair : forall pairs outs f, length outs = length pairs -> List.Forall f pairs -> List.Forall (fun x => f (Word x, ADTIn x)) (make_triples pairs outs).
  admit.
Qed.

Lemma make_triples_ADTIn : forall pairs outs, length outs = length pairs -> map ADTIn (make_triples pairs outs) = map snd pairs.
  admit.
Qed.

