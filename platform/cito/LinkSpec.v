Set Implicit Arguments.

Require Import GLabel GLabelMap GLabelMapFacts ConvertLabel GoodModule GoodFunction NameDecoration.
Export GLabel GLabelMap GLabelMapFacts ConvertLabel GoodModule GoodFunction NameDecoration.
Import GLabelMap.

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

    Definition label_in (lbl : glabel) :=
      (exists m f,
         List.In m modules /\
         List.In f (Functions m) /\
         lbl = (MName m, FName f)) \/
      In lbl imports.

    Definition label_mapsto lbl spec :=
      (exists ispec m f,
         spec = Internal ispec /\
         List.In m modules /\
         List.In f (Functions m) /\
         ispec = f /\ 
         lbl = (MName m, FName f)) \/
      (exists fspec,
         spec = Foreign fspec /\
         find lbl imports = Some fspec).

    Definition stn_good_to_use (stn : settings) :=
      forall lbl : glabel,
        label_in lbl ->
        Labels stn lbl <> None.

    Definition stn_injective (stn : settings) :=
      forall lbl1 lbl2 p, 
        label_in lbl1 -> 
        label_in lbl2 -> 
        Labels stn lbl1 = Some p -> 
        Labels stn lbl2 = Some p -> 
        lbl1 = lbl2.

    Definition fs_good_to_use (fs : settings -> W -> option Callee) (stn : settings) :=
      forall p spec, 
        fs stn p = Some spec <-> 
        exists lbl : glabel,
          Labels stn lbl = Some p /\
          label_mapsto lbl spec.

    Definition env_good_to_use stn fs :=
      stn_good_to_use stn /\
      stn_injective stn /\
      fs_good_to_use fs stn.

    Definition func_export_IFS m (f : GoodFunction) := ((MName m, FName f), f : InternalFuncSpec).
        
    Definition module_exports_IFS m := 
      List.map (func_export_IFS m) (Functions m).

    Require Import ListFacts1.

    Definition exports_IFS :=
      to_map
        (app_all 
           (List.map module_exports_IFS modules)).

    Section fs.

      Variable stn : settings.

      Definition labels (lbl : glabel) : option W := Labels stn lbl.

      Definition is_label_map_to_word lbl p :=
        match labels lbl with
          | Some p' => 
            if weq p p' then
              true
            else
              false
          | None => false
        end.

      Definition is_label_map_to_word' A p (x : glabel * A) := is_label_map_to_word (fst x) p.

      Definition find_by_word A m (p : W) : option A :=
        match List.find (is_label_map_to_word' p) m with
          | Some (_, a) => Some a
          | None => None
        end.

      Definition is_export := find_by_word (elements exports_IFS).

      Definition is_import := find_by_word (elements imports).

      Definition fs (p : W) : option Callee :=
        match is_export p with
          | Some spec => Some (Internal spec)
          | None => 
            match is_import p with
              | Some spec => Some (Foreign spec)
              | None => None
            end
        end.

    End fs.

  End TopSection.

  Require Import RepInv.

  Module Make (Import M : RepInv E).

    Require Import CompileFuncSpec.
    Module Import CompileFuncSpecMake := Make E M.
    Import InvMake2.
    Export CompileFuncSpec CompileFuncSpecMake InvMake2.

    Section TopSection.

      Variable modules : list GoodModule.

      Variable imps : t ForeignFuncSpec.

      Notation fs := (fs modules imps).
      
      Definition func_spec (id : glabel) f : assert := (st ~> name_marker id /\ [| env_good_to_use modules imps (fst st) fs |] ---> spec_without_funcs_ok f fs st)%PropX.

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