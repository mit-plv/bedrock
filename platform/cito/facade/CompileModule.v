Set Implicit Arguments.

Require Import FModule.
Require Import Compile.
Require Import Facade.
Require Import GoodFunction.
Require Import GoodModule.

Section ADTValue.

  Variable ADTValue : Type.

  Notation FModule := (@FModule ADTValue).

  Variable module : FModule.

  Require Import String.
  Local Open Scope string_scope.

  Definition is_good_module_name (s : string) := negb (prefix "_" s).

  Lemma is_good_module_name_sound_cito name : is_good_module_name name = true -> IsGoodModuleName name.
  Proof.
    unfold is_good_module_name, IsGoodModuleName.
    intros; eapply Bool.negb_true_iff; eauto.
  Qed.

  Variable m_name : string.

  Hypothesis good_name : is_good_module_name m_name = true.

  Notation FName := SyntaxFunc.Name.
  Notation MName := GoodModule.Name.

  Require Import GoodFunc.

  Lemma compile_GoodFunc f : GoodFunc (compile_op f).
    admit.
  Qed.

  Definition compile_func (name : string) (f : FFunction) : GoodFunction.
    refine
      ({|
          Fun := 
            {|
              SyntaxFunc.Name := name;
              SyntaxFunc.Core := compile_op f
            |};
          IsGoodFunc := _
        |}).
    simpl.
    eapply compile_GoodFunc.
  Defined.

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.

  Definition compile_funcs (funs : StringMap.t FFunction) := List.map (uncurry compile_func) (elements funs).

  Lemma NoDup_elements elt (m : StringMap.t elt) : NoDup (List.map fst (elements m)).
  Proof.
    eapply NoDupKey_NoDup_fst.
    eapply elements_3w.
  Qed.

  Definition compile : GoodModule.
    refine 
      ({|
          Name := m_name;
          GoodModuleName := _;
          Functions := compile_funcs (FModule.Functions module);
          NoDupFuncNames := _
        |}).
    eapply is_good_module_name_sound_cito; eauto.
    unfold compile_funcs.
    unfold uncurry.
    rewrite map_map.
    unfold compile_func.
    simpl.
    eapply NoDup_elements.
  Defined.

End ADTValue.