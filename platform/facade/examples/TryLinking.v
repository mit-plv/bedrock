Set Implicit Arguments.

Require Import DFacadeToBedrock.
Require Import FiatADTs.
Require Import FiatRepInv.

Module Import M := DFacadeToBedrock.Make FiatADTs.Adt FiatRepInv.Ri.

Definition pre_cond (arg1 : Value ADTValue) (arg2 : Value ADTValue) := False.
Definition post_cond (arg1 : Value ADTValue) (arg2 : Value ADTValue) (ret : Value ADTValue) := True.

Require Import CompileUnit.

Definition imports := GLabelMapFacts.of_list ((("ADT", "sEmpty"), FEnsemble_sEmpty) :: nil).

Definition unit : CompileUnit pre_cond post_cond.
  refine (@Build_CompileUnit _ pre_cond post_cond (DFacade.Assign "ret" (Const $0)) eq_refl eq_refl eq_refl imports eq_refl _ _).
  intros.
  unfold pre_cond in *; intuition.
  intros.
  unfold pre_cond in *; intuition.
Defined.

Definition output := compile unit.
Definition m1 := CompileOutMake.bedrock_module output.
Definition m1_ok := CompileOutMake.bedrock_module_ok output.
Definition m2 := CompileOutMake.bedrock_module_impl output.
Definition m2_ok := CompileOutMake.bedrock_module_impl_ok output.

Definition all1 := link m1 m2.

Lemma all1_ok : moduleOk all1.
  Import LinkMake.LinkModuleImplsMake.

  Ltac link_simp2 :=
    simpl Imports; 
    simpl Exports; 
    unfold CompileModuleMake.mod_name; 
    unfold impl_module_name;
    simpl GName; 
    simpl append; 
    unfold CompileModuleMake.imports;
    unfold LinkMake.StubsMake.StubMake.bimports_diff_bexports, LinkMake.StubsMake.StubMake.bimports_diff_bexports;
    unfold diff_map, GLabelMapFacts.diff_map; 
    simpl List.filter;
    unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export, LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export;
    unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label, LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label;
    simpl GName; 
    unfold impl_module_name; 
    simpl append; 
    simpl IsGoodModule.FName; 
    unfold CompileModuleMake.mod_name; 
    unfold impl_module_name;
    unfold LinkMake.StubsMake.StubMake.bimports_diff_bexports;
    unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export;
    unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label;
    unfold impl_module_name; 
    unfold CompileModuleMake.imports.

  Ltac link2 ok1 ok2 :=
    eapply linkOk; [ eapply ok1 | eapply ok2
                     | reflexivity
                     | link_simp2; link_simp; eauto ..
                   ].

  link2 m1_ok m2_ok.
Qed.

Require Import FiatImpl.

Definition all := link all1 FiatImpl.m.

Theorem all_ok : moduleOk all.
  link2 all1_ok FiatImpl.ok.
Qed.