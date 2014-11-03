Set Implicit Arguments.

Require Import String.
Local Open Scope string_scope.
Require Import StringMap.
Import StringMap.

Require Import Facade.

Definition FunCore := OperationalSpec.

Definition is_syntactic_wellformed (f : FunCore) := true.

Record FFunction :=
  {
    Core : FunCore;
    syntactic_wellformed : is_syntactic_wellformed Core = true
  }.
    
Definition is_good_module_name (s : string) := negb (prefix "_" s).

Section ADTValue.

  Variable ADTValue : Type.

  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).

  Record FModule := 
    {
      Name : string;
      good_name : is_good_module_name Name = true;
      Imports : StringMap.t AxiomaticSpec;
      (* Exports : StringMap.t AxiomaticSpec; *)
      Functions : StringMap.t FFunction
    }.

End ADTValue.