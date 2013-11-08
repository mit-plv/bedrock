Require Import Syntax Semantics.
Require Import CompileStatement.

Set Implicit Arguments.

Definition is_good_optimizer optimizer :=
  (forall fs s v vs' heap', RunsTo fs (optimizer s) v (vs', heap') -> exists vs'', RunsTo fs s v (vs'', heap')) /\ 
  (forall fs s v, Safety.Safe fs s v -> Safety.Safe fs (optimizer s) v) /\
  (forall s, List.incl (SemanticsLemmas.footprint (optimizer s)) (SemanticsLemmas.footprint s)) /\
  (forall s, CompileStatement.depth (optimizer s) <= CompileStatement.depth s).

