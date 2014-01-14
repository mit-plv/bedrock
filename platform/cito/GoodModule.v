Set Implicit Arguments.

Require Import GoodFunction.
Record GoodModule :=
  {
    Name : string;
    Functions : list GoodFunction;
    NoDupFuncNames : NoDup (map (fun f => SyntaxFunc.Name (proj1_sig f)) Functions)
  }.

Require Import SyntaxModule.
Definition is_good_module module := 
  NoDup (map SyntaxFunc.Name (SyntaxModule.Functions module)) /\
  List.Forall GoodFunc (Functions module).

Definition to_prod_list : forall A P (ls : list A), List.Forall P ls -> list { x | P x }.
  induction ls.
  econstructor 1.
  econstructor 2.
  econstructor; inversion H; subst; eauto.
  eapply IHls; inversion H; subst; eauto.
Defined.

Lemma to_prod_list_proj1 : forall A ls P (H : List.Forall P ls), List.map (@proj1_sig _ P)(@to_prod_list A _ _ H) = ls.
  induction ls; simpl; intuition.
Qed.

Definition to_good_module m : is_good_module m -> GoodModule.
  intros.
  destruct H.
  econstructor.
  eapply (SyntaxModule.Name m).
  instantiate (1 := to_prod_list H0).
  erewrite <- map_map.
  erewrite to_prod_list_proj1.
  eauto.
Defined.