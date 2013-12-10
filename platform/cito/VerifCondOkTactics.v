Require Import AutoSep.
Require Import ListFacts.
Require Import Safe.
Require Import Inv.

Local Open Scope nat.

Ltac hide_upd_sublist :=
  repeat match goal with
           | H : context [ upd_sublist ?L _ _ ] |- _ => set (upd_sublist L _ _) in *
         end.

Lemma replace1 : forall a b c d e : W, a ^+ b ^+ c ^+ d ^+ e = a ^+ (b ^+ c ^+ d ^+ e).
  intros; repeat rewrite wplus_assoc in *; eauto.
Qed.

Lemma replace_it3 : forall a b, 2 <= a -> b <= a - 2 -> $(a) ^- $(S (S b)) = natToW (a - 2 - b).
  intros; replace (a - 2 - b) with (a - (2 + b)) by omega; rewrite natToW_minus; eauto.
Qed.

Ltac inversion_Safe :=
  repeat match goal with
           | H : Safe _ _ _ |- _ => inversion H; clear H; subst
         end.

Transparent funcs_ok.
Ltac unfold_funcs_ok :=
  match goal with 
    | H : interp _ (funcs_ok _ _ _) |- _ => generalize H; intro is_funcs_ok; unfold funcs_ok in H
  end.
Opaque funcs_ok.

Ltac specialize_funcs_ok :=
  match goal with
    | H : context [ (_ ---> _)%PropX ], H2 : _ = Some _ |- _ => 
      specialize (Imply_sound (H _ _) (Inj_I _ _ H2)); propxFo
  end.

Ltac hide_map :=
  repeat match goal with
           | H : context [ map ?A _ ] |- _ => set (map A _) in *
         end.

Ltac auto_apply :=
  match goal with
      H : _ |- _ => eapply H
  end.