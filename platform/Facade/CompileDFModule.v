Set Implicit Arguments.

Require Import Platform.Facade.DFModule.
Require Import Platform.Facade.CompileDFacade.
Require Import Platform.Facade.DFacade.

Section ADTValue.

  Variable ADTValue : Type.

  Variable module : DFModule ADTValue.

  Definition compile_func (f : DFFun) : FModule.FFunction := FModule.Build_FFunction (compile_op f) (compiled_syntax_ok f).

  Require Import Platform.Cito.StringMap.
  Import StringMap.
  Require Import Platform.Cito.StringMapFacts.

  Definition compile_to_fmodule : FModule.FModule ADTValue := FModule.Build_FModule (Imports module) (StringMap.map compile_func (Funs module)).

  Require Import Coq.Strings.String.

  Variable name : string.

  Require Import Platform.Cito.NameDecoration.

  Hypothesis good_name : is_good_module_name name = true.

  Require Platform.Facade.CompileModule.

  Definition compile_to_gmodule : GoodModule.GoodModule := CompileModule.compile_to_gmodule compile_to_fmodule name good_name.

End ADTValue.