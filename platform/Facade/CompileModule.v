Set Implicit Arguments.

Require Import FModule.
Require Import Compile.
Require Import Facade.

Section ADTValue.

  Variable ADTValue : Type.

  Variable module : FModule ADTValue.

  Require Import GoodModule.

  Notation FName := SyntaxFunc.Name.
  Notation MName := GoodModule.Name.

  Require Import CModule.
  Require Import Semantics.

  Definition compile_func (f : FFunction) : CFun := Build_CFun (compile_op f) (syntax_ok f).

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.

  Definition compile_to_cmodule : CModule := Build_CModule (StringMap.map compile_func (FModule.Functions module)).

  Require Import String.

  Variable name : string.

  Require Import Cito.NameDecoration.

  Hypothesis good_name : is_good_module_name name = true.

  Require Import CModuleFacts.

  Definition compile_to_gmodule : GoodModule.GoodModule := cmodule_to_gmodule name good_name compile_to_cmodule.

End ADTValue.