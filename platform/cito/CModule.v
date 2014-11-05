Set Implicit Arguments.

Require Import GoodModuleDec.
Require Import FuncCore.

Record CFun :=
  {
    Core : FuncCore;
    good_func : is_good_func Core = true
  }.
    
Coercion Core : CFun >-> FuncCore.

Require Import StringMap.

Record CModule := 
  {
    Funs : StringMap.t CFun
  }.

Require Import GoodModuleDec.
Require Import GoodModule.
Require Import GoodFunction.

Definition cfun_to_gfun (name : string) (f : CFun) : GoodFunction.
  refine (Build_GoodFunction (Build_Func name f) _).
  destruct f; simpl in *.
  eapply is_good_func_sound; eauto.
Defined.

Require Import StringMap.
Require Import StringMapFacts.

Definition cfuns_to_gfuns (fs : StringMap.t CFun) : list GoodFunction := List.map (uncurry cfun_to_gfun) (StringMap.elements fs).

Require Import NameDecoration.

Lemma cfuns_to_gfuns_nodup fs : NoDup (List.map (fun (f : GoodFunction) => SyntaxFunc.Name f) (cfuns_to_gfuns fs)).
Proof.
  unfold cfuns_to_gfuns.
  rewrite map_map.
  simpl.
  eapply NoDup_elements; eauto.
Qed.

Definition cmodule_to_gmodule name (H : is_good_module_name name = true) (m : CModule) : GoodModule.GoodModule.
  refine (@Build_GoodModule name _ (cfuns_to_gfuns (Funs m)) _).
  eapply is_good_module_name_sound; eauto.
  eapply cfuns_to_gfuns_nodup.
Defined.

