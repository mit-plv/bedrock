Set Implicit Arguments.

Require Import Equalities.

Module Key' <: MiniDecidableType.

  Require Import Memory.

  Definition t := W.

  Require Import Word.

  Definition eq_dec := @weq 32.

End Key'.

Module Key := Make_UDT Key'.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import FMapWeakList.

  Module Import M := Make Key.

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