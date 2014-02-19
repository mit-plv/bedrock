Set Implicit Arguments.

Require Import ADT.
Require Import RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import AutoSep.
  Require Import StructuredModule.
  Require Import StructuredModuleFacts.
  Require Import GoodModule.
  Require Import GoodFunction.
  Require Import ConvertLabel.
  Require Import NameDecoration.
  Require Import Wrap.
  Require Import GeneralTactics.
  Require Import GeneralTactics2.
  Require Import StringFacts.
  
  Require Import Stubs.
  Module Import StubsMake := Make E M.
  Require Import Stub.
  Import StubMake.
  Require Import CompileFuncSpec.
  Import CompileFuncSpecMake.
  Require Import Inv.
  Import InvMake.
  Require Import Semantics.
  Import SemanticsMake.
  Import InvMake2.

  Require Import FMapFacts1.
  Require Import FMapFacts3.

  Require Import ConvertLabelMap.
  Import Notations.
  Open Scope clm_scope.

  Require LabelMap.
  Module BLM := LabelMap.LabelMap.
  Module BLK := LabelMap.LabelKey.
  Require Import Equalities.
  Module BLK_as_UDT := Make_UDT BLK.
  Module Import BLMFU3 := FMapFacts3.UWFacts_fun BLK_as_UDT BLM.
  Module Import BLMFU := UWFacts.
  Module Import BLMF := WFacts.

  Require Import Label.
  Module LM := LabelMap.
  Module Label_as_UDT := Key'.
  Module Import LMFU3 := FMapFacts3.UWFacts_fun Label_as_UDT LM.
  Module Import LMFU := UWFacts.
  Module Import LMF := WFacts.
  Require Import ListFacts2.
  Module LF := ListFacts2.
  Module Import LFL := Make Label_as_UDT.

  Require Import ListFacts3.

  Module Import SS := StringSet.StringSet.
  Module Import SSF := StringSet.StringFacts.
  Module SSK := StringSet.StringKey.
  Require Import FSetFacts1.
  Module SSK_as_UDT := Make_UDT SSK.
  Module Import SSUF := UWFacts_fun SSK_as_UDT SS.

  Import LM.
  Import P.
  Import F.

  Section TopSection.

    (* modules to be linked *)
    Variable modules : list GoodModule.

    Hypothesis ModulesNotEmpty : modules <> nil.

    Hypothesis NoDupModuleNames : List.NoDup (module_names modules).

    (* imported specs *)
    Variable imports : t ForeignFuncSpec.

    Hypothesis NoSelfImport : LF.Disjoint (module_names modules) (imported_module_names imports).

    Hypotheses ImportsGoodModuleName : forall l, In l imports -> IsGoodModuleName (fst l).

