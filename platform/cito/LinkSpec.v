Set Implicit Arguments.

Require Import GLabel GLabelMap GLabelMapFacts ConvertLabel GoodModule GoodFunction NameDecoration.
Export GLabel GLabelMap GLabelMapFacts ConvertLabel GoodModule GoodFunction NameDecoration.
Import GLabelMap.
Require Import AutoSep.

Definition name_marker (id : glabel) : PropX W (settings * state) := (Ex s, [| s = id |])%PropX.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Semantics.
  Module Import SemanticsMake := Make E.
  Export Semantics SemanticsMake.

  Section TopSection.

    Variable modules : list GoodModule.

    Variable imports : t ForeignFuncSpec.

    Notation FName := SyntaxFunc.Name.
    Notation MName := GoodModule.Name.

    Definition stn_good_to_use (stn : settings) :=
      forall lbl : glabel,
        ((exists m f,
            List.In m modules /\
            List.In f (Functions m) /\
            lbl = (MName m, FName f)) \/
         In lbl imports) ->
        Labels stn lbl <> None.

    Definition fs_good_to_use (fs : settings -> W -> option Callee) (stn : settings) :=
      forall p spec, 
        fs stn p = Some spec <-> 
        exists lbl : glabel,
          Labels stn lbl = Some p /\
          ((exists ispec m f,
              spec = Internal ispec /\
              List.In m modules /\
              List.In f (Functions m) /\
              ispec = f /\ 
              lbl = (MName m, FName f)) \/
           (exists fspec,
              spec = Foreign fspec /\
              find lbl imports = Some fspec)).

  End TopSection.

  Require Import RepInv.

  Module Make (Import M : RepInv E).

    Require Import CompileFuncSpec.
    Module Import CompileFuncSpecMake := Make E M.
    Import InvMake2.
    Export CompileFuncSpec CompileFuncSpecMake InvMake2.

    Section TopSection.

      Variable fs : settings -> W -> option Callee.

      Variable modules : list GoodModule.

      Variable imps : t ForeignFuncSpec.

      Definition func_spec (id : glabel) f : assert := (st ~> name_marker id /\ [| stn_good_to_use modules imps (fst st) /\ fs_good_to_use modules imps fs (fst st) |] ---> spec_without_funcs_ok f fs st)%PropX.

      Definition foreign_func_spec id spec : assert := 
        st ~> name_marker id /\ ExX, foreign_spec _ spec st.

      Definition imports := mapi (foreign_func_spec) imps.

      Notation FName := SyntaxFunc.Name.
      Notation MName := GoodModule.Name.

      Definition func_export module (f : GoodFunction) :=
        let lbl := (MName module, FName f) in
        (lbl, func_spec lbl f).

      Definition module_exports m := 
        of_list
          (List.map 
             (func_export m)
             (Functions m)).

      Definition exports := update_all (List.map module_exports modules).

      Definition impl_label mod_name f_name : glabel := (impl_module_name mod_name, f_name).

      Definition func_impl_export m (f : GoodFunction) := (impl_label (MName m) (FName f), spec f).

      Definition module_impl_exports m := 
        of_list
          (List.map 
             (func_impl_export m)
             (Functions m)).

      Definition impl_exports := update_all (List.map module_impl_exports modules).

      Definition all_exports := update exports impl_exports.

    End TopSection.

  End Make.

End Make.