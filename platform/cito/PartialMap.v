Require Import Equalities.

Set Implicit Arguments.

Module Type PartialMap (Key : MiniDecidableType) (Data : Typ).

  Delimit Scope pmap_scope with pmap.

  Local Open Scope pmap_scope.

  Parameter pmap : Type.

  Parameter sel : pmap -> Key.t -> option Data.t.

  Parameter add : pmap -> Key.t * Data.t -> pmap.
  Infix "+" := add : pmap_scope.

  Parameter remove : pmap -> Key.t -> pmap.
  Infix "-" := remove : pmap_scope.

  Parameter sel_remove_eq : forall m x, sel (m - x) x = None.

  Parameter sel_remove_ne : forall m x x', x <> x' -> sel (m - x) x' = sel m x'.

  Parameter sel_add_eq : forall m x w, sel (m + (x, w)) x = Some w.

  Parameter sel_add_ne : forall m x w x', x <> x' -> sel (m + (x, w)) x' = sel m x'.

  Parameter empty : pmap.
  Notation "[]" := empty : pmap_scope.

  Parameter empty_correct : forall x, sel [] x = None.

End PartialMap.

Module MakeSubmap (Key : MiniDecidableType) (Data : Typ) (M : PartialMap Key Data) <: PartialMap Key Data.

  Include M.

  Definition submap (a b : pmap) := forall x w, sel a x = Some w -> sel b x = Some w.
  Infix "<=" := submap : pmap_scope.

  Lemma submap_correct : forall a b, submap a b -> forall x w, sel a x = Some w -> sel b x = Some w.
    eauto.
  Qed.

  Lemma empty_submap : forall m, submap empty m.
    unfold submap; intros; rewrite empty_correct in H; discriminate.
  Qed.

End MakeSubmap.

(* Implementations *)

Module ArrowPMap (Key : MiniDecidableType) (Data : Typ) <: PartialMap Key Data.

  Definition pmap := Key.t -> option Data.t.

  Definition sel (m : pmap) := m.

  Definition add (m : pmap) (p : Key.t * Data.t) : pmap :=
    fun k =>
      if Key.eq_dec k (fst p) then
        Some (snd p)
      else
        m k.

  Definition remove (m : pmap) (k : Key.t) : pmap :=
    fun k' =>
      if Key.eq_dec k' k then
        None
      else
        m k'.

  Lemma sel_remove_eq : forall m x, sel (remove m x) x = None.
    unfold sel, remove; intros; destruct (Key.eq_dec x x); intuition.
  Qed.
    
  Lemma sel_remove_ne : forall m x x', x <> x' -> sel (remove m x) x' = sel m x'.
    unfold sel, remove; intros; destruct (Key.eq_dec x' x); subst; intuition.
  Qed.

  Lemma sel_add_eq : forall m x w, sel (add m (x, w)) x = Some w.
    unfold sel, add; simpl; intros; destruct (Key.eq_dec x x); intuition.
  Qed.

  Lemma sel_add_ne : forall m x w x', x <> x' -> sel (add m (x, w)) x' = sel m x'.
    unfold sel, add; simpl; intros; destruct (Key.eq_dec x' x); subst; intuition.
  Qed.

  Definition empty : pmap := fun _ => None.

  Lemma empty_correct : forall x, sel empty x = None.
    eauto.
  Qed.

End ArrowPMap.