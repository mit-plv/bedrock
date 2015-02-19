Set Implicit Arguments.

Require Import DFModule.
Require Import CompileDFacade.
Require Import DFacade.

Section ADTValue.

  Variable ADTValue : Type.

  Variable module : DFModule ADTValue.

  Definition compile_func (f : DFFun) : FModule.FFunction := FModule.Build_FFunction (compile_op f) (compiled_syntax_ok f).

  Require Import StringMap.
  Import StringMap.
  Require Import StringMapFacts.

  Definition compile_to_fmodule : FModule.FModule ADTValue := FModule.Build_FModule (Imports module) (StringMap.map compile_func (Funs module)).

  Require Import String.

  Variable name : string.

  Require Import Cito.NameDecoration.

  Hypothesis good_name : is_good_module_name name = true.

  Require CompileModule.

  Definition compile_to_gmodule : GoodModule.GoodModule := CompileModule.compile_to_gmodule compile_to_fmodule name good_name.

End ADTValue.