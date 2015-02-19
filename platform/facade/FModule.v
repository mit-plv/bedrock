Set Implicit Arguments.

Require Import StringMap.
Import StringMap.

Require Import Facade.
Require Import Compile.
Require Import Semantics.
Require Import GoodModuleDec.

Local Notation FunCore := OperationalSpec.

Definition is_syntax_ok (f : FunCore) := is_good_func (compile_op f).

Record FFunction :=
  {
    Core : FunCore;
    syntax_ok : is_syntax_ok Core = true
  }.
    
Coercion Core : FFunction >-> OperationalSpec.

Section ADTValue.

  Variable ADTValue : Type.

  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).

  Require Import GLabelMap.

  Record FModule := 
    {
      Imports : GLabelMap.t AxiomaticSpec;
      (* Exports : StringMap.t AxiomaticSpec; *)
      Functions : StringMap.t FFunction
    }.

End ADTValue.