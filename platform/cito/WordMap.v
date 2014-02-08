Set Implicit Arguments.

(*
Require Import Equalities.

Module Key' <: MiniDecidableType.

  Require Import Memory.

  Definition t := W.

  Require Import Word.

  Definition eq_dec := @weq 32.

End Key'.

Module Key := Make_UDT Key'.
 *)

Require Import OrderedType.

Module W_as_MOT <: MiniOrderedType.

  Require Import Memory.

  Definition t := W.

  Require Import Word.

  Definition eq := @eq t.

  Local Open Scope nat.

  Definition lt (x y : t) := wordToNat x < wordToNat y.

  Lemma eq_refl : forall x : t, eq x x.
    unfold eq; eauto.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    unfold eq; eauto.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    unfold eq; intuition.
    congruence.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    unfold lt; intros; omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    unfold lt; unfold eq; intuition.
    subst.
    omega.
  Qed.

  Require Import WordFacts.

  Definition compare : forall x y : t, Compare lt eq x y.
    unfold lt; unfold eq.
    intros.
    destruct (Compare_dec.lt_eq_lt_dec (wordToNat x) (wordToNat y)).
    destruct s.
    econstructor 1; eauto.
    econstructor 2; eauto.
    eapply wordToNat_eq_eq; eauto.
    econstructor 3; eauto.
  Defined.

End W_as_MOT.

Module W_as_OT := MOT_to_OT W_as_MOT.

Require Import FMapAVL.

Module Import WordMap := Make W_as_OT.

Require Import FMapFacts.

Module Import Facts := WFacts_fun W_as_OT WordMap.
Module Import Properties := WProperties_fun W_as_OT WordMap.


(*
Require Import ADT.

Module Make (Import E : ADT).

  Definition elt := ADTValue.

  Definition Heap := t elt.

  Implicit Types m h : Heap.
  Implicit Types x y z k p w : key.
  Implicit Types e v a : elt.
  Implicit Types ls : list (key * elt).

  Definition heap_sel h p := find p h.

  Definition heap_mem := @In elt.

  Definition heap_upd h p v := add p v h.

  Definition heap_remove h p := remove p h.

  Definition heap_empty := @empty elt.

  Require Import FMapFacts.

  Module Import F := WFacts_fun Key M.
  Module Import P := WProperties_fun Key M.

  Definition heap_merge := @update elt.

  Definition heap_elements := @elements elt.

  Definition heap_diff := @diff elt.

End Make.
 *)