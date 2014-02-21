Set Implicit Arguments.

Require Import DecidableType.
Require Import FMapInterface.

Module WFacts_fun (E:DecidableType)(Import M:WSfun E).

  Require Import FMapFacts.

  Module Import F := WFacts_fun E M.
  Module Import P := WProperties_fun E M.

  Section Elt.
    Variable elt:Type.

    Implicit Types m : t elt.
    Implicit Types x y z k : key.
    Implicit Types e v : elt.
    Implicit Types ls : list (key * elt).

    Notation eqke := (@eq_key_elt elt).
    Notation eqk := (@eq_key elt).
    
    Lemma update_with_empty : forall m, update m (@empty _) = m.
      unfold update; intros.
      rewrite fold_1.
      rewrite elements_empty.
      reflexivity.
    Qed.

  End Elt.

End WFacts_fun.