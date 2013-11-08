Require Import SetModule PartialMap.
Require Import Equalities.

Set Implicit Arguments.

Module Type HasSubtract (Key : MiniDecidableType) (Data : Typ) (S : Set_ Key) <: PartialMap Key Data.

  Include PartialMap.PartialMap Key Data.

  Local Open Scope pmap_scope.

  Parameter subtract : pmap -> S.set -> pmap.
  Infix "--" := subtract (at level 60) : pmap_scope.

  Parameter subtract_none : forall m s x, S.mem x s -> sel (m -- s) x = None.

  Parameter subtract_in : forall m s x w, sel (m -- s) x = Some w -> sel m x = Some w.

End HasSubtract.

(* Implementations *)

Module ArrowHasSubtract (Key : MiniDecidableType) (Data : Typ) (S : MembershipDecidableSet Key) <: HasSubtract Key Data S.

  Include ArrowPMap Key Data.

  Definition subtract (m : pmap) (s : S.set) : pmap :=
    fun k =>
      if S.mem_dec k s then
        None
      else
        sel m k.

  Lemma subtract_none : forall m s x, S.mem x s -> sel (subtract m s) x = None.
    unfold subtract, sel; intros; destruct (S.mem_dec x s); intuition.
  Qed.

  Lemma subtract_in : forall m s x w, sel (subtract m s) x = Some w -> sel m x = Some w.
    unfold subtract, sel; intros; destruct (S.mem_dec x s); intuition; discriminate.
  Qed.

End ArrowHasSubtract.

Module SubtractSubmap (Key : MiniDecidableType) (Data : Typ) (S : MembershipDecidableSet Key) (M : HasSubtract Key Data S) <: HasSubtract Key Data S.

  Include M.

  Module Submap := MakeSubmap Key Data M.

  Lemma subtract_submap : forall (a : pmap) (b : S.set), Submap.submap (subtract a b) a.
    unfold Submap.submap; intros; eapply subtract_in; eauto.
  Qed.

End SubtractSubmap.