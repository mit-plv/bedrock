Set Implicit Arguments.

Require Import DFacade DFModule.
Require Import StringMap WordMap GLabelMap.

Notation module_name := "dfmodule".
Notation fun_name := "dffun".
Notation argvar1 := "arg1".
Notation argvar2 := "arg2".
Notation argvars := (argvar1 :: argvar2 :: nil).
Notation retvar := "ret".

Record CompileUnit (ADTValue : Type) := 
  {
    (* the DFacade program *)
    prog : Stmt;
    (* syntax checks, can be discharged by eq_refl for concrete prog *)
    no_assign_to_args : is_disjoint (assigned prog) (StringSetFacts.of_list argvars) = true;
    syntax_ok : is_syntax_ok prog = true;
    compile_syntax_ok : FModule.is_syntax_ok (CompileDFacade.compile_op (Build_OperationalSpec argvars retvar prog eq_refl eq_refl no_assign_to_args eq_refl eq_refl syntax_ok)) = true;
    (* imported axiomatic specs *)
    imports : GLabelMap.t (AxiomaticSpec ADTValue);
    (* pre_cond arg1 arg2 *)
    pre_cond : Value ADTValue -> Value ADTValue -> Prop;
    (* post_cond arg1 arg2 ret *)
    post_cond : Value ADTValue -> Value ADTValue -> Value ADTValue -> Prop;
    (* correctness conditions *)
    pre_safe : forall st value1 value2, 
                 StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) -> 
                 pre_cond value1 value2 -> 
                 DFacade.Safe (GLabelMap.map (@Axiomatic _) imports) prog st;
    pre_runsto_post : forall st st' value1 value2, 
                        StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) -> 
                        pre_cond value1 value2 -> DFacade.RunsTo (GLabelMap.map (@Axiomatic _) imports) prog st st' -> 
                        exists ret, StringMap.Equal st' (StringMapFacts.make_map (retvar :: nil) (ret :: nil)) /\ post_cond value1 value2 ret
  }.

