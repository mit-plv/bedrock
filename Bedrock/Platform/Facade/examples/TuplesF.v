(** Multisets of tuples *)

Require Import Bedrock Ensembles Relations.

(* This section copied from Fiat for convenience, to avoid circular dependencies across libraries! *)
Section IndexedEnsembles.
  Context {ElementType : Type}.

  Record IndexedElement :=
    { elementIndex : nat;
      indexedElement : ElementType }.

  Definition IndexedEnsemble := Ensemble IndexedElement.

  Definition IndexedEnsemble_In
             (ensemble : IndexedEnsemble)
             (item : ElementType) :=
    exists idx, Ensembles.In _ ensemble {| elementIndex := idx; indexedElement := item |}.

  Definition IndexedEnsembleSubtract
             (element : ElementType)
             (ens : IndexedEnsemble)
  : IndexedEnsemble :=
    fun element' => indexedElement element' <> element /\ ens element'.

  (* 'Deleting' a set of tuples [R] from a relation [F] is the same
   as taking the intersection of [F] and the complement of [R]. *)
  Definition EnsembleDelete
             (F : IndexedEnsemble)
             (R : Ensemble ElementType)
    := Intersection _ F (Complement _ (fun iel => R (indexedElement iel))).

  Definition IndexedEnsembleUpdate
             (ens : IndexedEnsemble)
             (cond : Ensemble ElementType)
             (updateR : relation ElementType)
  : IndexedEnsemble
    := fun e => (exists f: IndexedElement, ((ens f) /\ cond (indexedElement f) /\ updateR (indexedElement f) (indexedElement e))
                                           /\ elementIndex e = elementIndex f) \/
                ((ens e) /\ Complement _ (fun f => cond (indexedElement f)) e).

  Definition UnIndexedEnsembleListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType)  :=
    exists l', (map indexedElement l') = l /\
               (forall x, Ensembles.In _ ensemble x <-> List.In x l') /\
               NoDup (map elementIndex l').

  Definition UnConstrFreshIdx
             (ensemble : IndexedEnsemble)
             (bound : nat) :=
  forall element,
    ensemble element
    -> lt (elementIndex element) bound.

  Definition EnsembleIndexedListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType) :=
    (exists bound, UnConstrFreshIdx ensemble bound)
    /\ UnIndexedEnsembleListEquivalence ensemble l.
End IndexedEnsembles.

Definition tupl := list W.
Definition tuples := @IndexedEnsemble tupl.

Definition EnsembleInsert {A : Type}
           (a : A)
           (R : Ensemble A)
           (a' : A) :=
  a' = a \/ R a'.

Lemma in_ensemble_insert_iff :
  forall {A} table tup inserted,
    In A (EnsembleInsert inserted table) tup <->
    tup = inserted \/ In A table tup.
Proof.
  firstorder.
Qed.

Definition insert (ts : tuples) (t : tupl) (ts' : tuples) : Prop :=
  exists idx,
    (forall t', In _ ts t' -> elementIndex t' <> idx)
    /\ ts' = EnsembleInsert {| elementIndex := idx;
                               indexedElement:= t |} ts.
