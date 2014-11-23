Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Semantics.
  Require Import List.

  Fixpoint make_triples pairs (outs : list (option ADTValue)) : list (ArgTriple ADTValue) :=
    match pairs, outs with
      | p :: ps, o :: os => {| Word := fst p; ADTIn := snd p; ADTOut := o |} :: make_triples ps os
      | _, _ => nil
    end.

  Require Import Memory.
  Require Import WordMap.
  Import WordMap.

  Definition store_pair heap (p : W * Value ADTValue) :=
    match snd p with
      | SCA _ => heap
      | ADT a => add (fst p) a heap
    end.

  Definition make_heap pairs := fold_left store_pair pairs (@empty _).

End ADTValue.