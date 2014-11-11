Set Implicit Arguments.

Require Import DFacade DFModule.
Require Import StringMap WordMap GLabelMap.

Notation module_name := "dfmodule".
Notation fun_name := "dffun".
Notation argvar1 := "arg1".
Notation argvar2 := "arg2".
Notation argvars := (argvar1 :: argvar2 :: nil).
Notation retvar := "ret".

Section TopSection.

  Variable ADTValue : Type.
  (* pre_cond arg1 arg2 *)
  Variable pre_cond : Value ADTValue -> Value ADTValue -> Prop.
  (* post_cond arg1 arg2 ret *)
  Variable post_cond : Value ADTValue -> Value ADTValue -> Value ADTValue -> Prop.

  Record CompileUnit := 
    {
      (* the DFacade program *)
      prog : Stmt;
      (* syntax checks, can be discharged by eq_refl for concrete prog *)
      no_assign_to_args : is_disjoint (assigned prog) (StringSetFacts.of_list argvars) = true;
      syntax_ok : is_syntax_ok prog = true;
      compile_syntax_ok : FModule.is_syntax_ok (CompileDFacade.compile_op (Build_OperationalSpec argvars retvar prog eq_refl eq_refl no_assign_to_args eq_refl eq_refl syntax_ok)) = true;
      (* imported axiomatic specs *)
      imports : GLabelMap.t (AxiomaticSpec ADTValue);
      (* correctness conditions *)
      pre_safe : 
        forall st value1 value2, 
          StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) -> 
          pre_cond value1 value2 -> 
          DFacade.Safe (GLabelMap.map (@Axiomatic _) imports) prog st;
      pre_runsto_post : 
        forall st st' value1 value2, 
          StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) -> 
          pre_cond value1 value2 -> DFacade.RunsTo (GLabelMap.map (@Axiomatic _) imports) prog st st' -> 
          exists ret, StringMapFacts.Submap (StringMapFacts.make_map (retvar :: nil) (ret :: nil)) st' /\ (forall x, x <> retvar -> not_mapsto_adt x st' = true) /\ post_cond value1 value2 ret
    }.

End TopSection.

(* the exported Bedrock function and its spec is [export_module_name!fun_name@compileS] *)
Notation export_module_name := "export".
Notation extra_stack := 20.

Require Import ADT RepInv.
Module Make (Import E : ADT) (Import M : RepInv E).
  Require Import Inv Malloc.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Require Import Semantics.

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
        bedrock_module : XCAP.module;
        bedrock_module_ok : XCAP.moduleOk bedrock_module;
        bedrock_module_export : LabelMap.find (export_module_name, Labels.Global fun_name) (Exports bedrock_module) = Some (Precondition compileS None)
      }.

  End TopSection.

End Make.