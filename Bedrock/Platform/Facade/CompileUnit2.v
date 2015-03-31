Set Implicit Arguments.

Require Import StringMap.
Require Import AxSpec.
Require Import DFModule.
Require Import String.
Require Import StringMapFacts.
Require Import Bedrock.Platform.Cito.NameDecoration.
Require Import GLabelMap.
Require Import ListFacts3.

Section TopSection.

  Variable ADTValue : Type.
  (* exported axiomatic specs *)
  Variable exports : StringMap.t (AxiomaticSpec ADTValue).

  Record CompileUnit :=
    {
      module : DFModule ADTValue;
      (* the name of the module that contains axiomatic export specs *)
      ax_mod_name : string;
      (* the name of the module that contains operational export specs *)
      op_mod_name : string;
      exports_in_domain : is_sub_domain exports (Funs module) = true;
      op_mod_name_ok : is_good_module_name op_mod_name = true;
      op_mod_name_not_in_imports :
        let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements (Imports module)) in
        List.forallb (fun x => negb (string_bool op_mod_name x)) imported_module_names = true;
      name_neq : negb (string_bool ax_mod_name op_mod_name) = true;
      proof : True (* placeholder, to be filled in later *)
    }.

End TopSection.
