Set Implicit Arguments.

Require Import CompileUnit.
Require Import StringMap WordMap GLabelMap String List.
Local Open Scope string_scope.

(* the exported Bedrock function and its spec is [export_module_name!fun_name@compileS] *)
Notation export_module_name := "export".
Notation extra_stack := 200.

Require Import ADT RepInv.
Module Make (Import E : ADT) (Import M : RepInv E).
  Require Import Inv Malloc.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Require Import Semantics.
  Require Import SemanticsUtil.

  Section TopSection.

    (* pre_cond arg1 arg2 *)
    Variable pre_cond : Value ADTValue -> Value ADTValue -> Prop.
    (* post_cond arg1 arg2 ret *)
    Variable post_cond : Value ADTValue -> Value ADTValue -> Value ADTValue -> Prop.

    Definition compileS := SPEC(argvar1, argvar2) reserving (6 + extra_stack)%nat
      Al v1, Al v2, Al h,                             
      PRE[V] is_heap h * [| pre_cond v1 v2 /\ let pairs := (V argvar1, v1) :: (V argvar2, v2) :: nil in disjoint_ptrs pairs /\ good_scalars pairs /\ WordMap.Equal h (make_heap pairs) |] * mallocHeap 0
      POST[R] Ex h', is_heap h' * [| exists r, post_cond v1 v2 r /\ let pairs := (R, r) :: nil in good_scalars pairs /\ WordMap.Equal h' (make_heap pairs) |] * mallocHeap 0.

    Require Import LabelMap.

    Record CompileOut :=
      {
        (* the main exported module to use *)
        bedrock_module : XCAP.module;
        bedrock_module_ok : XCAP.moduleOk bedrock_module;
        bedrock_module_export : LabelMap.find (export_module_name, Labels.Global fun_name) (Exports bedrock_module) = Some (Precondition compileS None);
        (* this is a module containing the actual code. Just link with this module. Don't need to care about it. *)
        bedrock_module_impl : XCAP.module;
        bedrock_module_impl_ok : XCAP.moduleOk bedrock_module_impl
      }.

  End TopSection.

End Make.