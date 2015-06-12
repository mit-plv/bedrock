Set Implicit Arguments.

Require Import StringMap.
Require Import AxSpec.
Require Import Bedrock.XCAP.

Section TopSection.

  Variable ADTValue : Type.
  (* exported axiomatic specs *)
  Variable exports : StringMap.t (AxiomaticSpec ADTValue).

  Record CompileOut (exports : StringMap.t (AxiomaticSpec ADTValue)) :=
    {
      (* the main exported module to use *)
      bedrock_module : XCAP.module;
      bedrock_module_ok : XCAP.moduleOk bedrock_module;
      (* this is a module containing the actual code. Just link with this module. Don't need to care about it. *)
      bedrock_module_impl : XCAP.module;
      bedrock_module_impl_ok : XCAP.moduleOk bedrock_module_impl
    }.

End TopSection.
