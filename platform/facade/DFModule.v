Set Implicit Arguments.

Require Import StringMap.
Import StringMap.

Require Import FModule.
Require Import DFacade.
Require Import CompileDFacade.

Local Notation FunCore := OperationalSpec.

Record DFFun :=
  {
    Core : FunCore;
    compiled_syntax_ok : FModule.is_syntax_ok (compile_op Core) = true
  }.
    
Coercion Core : DFFun >-> OperationalSpec.

Section ADTValue.

  Variable ADTValue : Type.

  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).

  Require Import GLabelMap.

  Record DFModule := 
    {
      Imports : GLabelMap.t AxiomaticSpec;
      (* Exports : StringMap.t AxiomaticSpec; *)
      Funs : StringMap.t DFFun
    }.

End ADTValue.