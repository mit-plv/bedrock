Require Import CompileFuncSpec.

Set Implicit Arguments.

Require Import Label.

Section TopSection.

  Require Import GoodModule.
  Variable modules : list GoodModule.

  Require Import Semantics.
  Variable imports : LabelMap.t ForeignFuncSpec.

  Definition FName := SyntaxFunc.Name.

  Definition MName := GoodModule.Name.

  Fixpoint flatten A (ls : list (list A)) :=
    match ls with
      | nil => nil
      | x :: xs => x ++ flatten xs
    end.

  Definition to_map B ls :=
    List.fold_left
      (fun m p => LabelMap.add (fst p) (snd p) m)
      ls (LabelMap.empty B).

  Require Import GoodFunction.
  Definition to_internal_func_spec (f : GoodFunction) : InternalFuncSpec :=
    {|
      Semantics.Fun := f;
      Semantics.NoDupArgVars := proj1 (IsGoodFunc f)
    |}.

  Coercion to_internal_func_spec : GoodFunction >-> InternalFuncSpec.

  Definition exports : LabelMap.t InternalFuncSpec :=
    to_map
      (flatten 
         (List.map 
            (fun m =>
               List.map 
                 (fun (f : GoodFunction) =>
                    ((MName m, FName f), f : InternalFuncSpec)
                 ) (Functions m)
            ) modules)).

  Definition accessible_labels := map fst (LabelMap.elements imports) ++ map fst (LabelMap.elements exports).

  Section fs.

    Variable stn : settings.

    Require Import ConvertLabel Label.
    Definition labels (lbl : label) : option W := Labels stn lbl.

    Definition is_label_map_to_word lbl p :=
      match labels lbl with
        | Some p' => 
          if weq p p' then
            true
          else
            false
        | None => false
      end.

    Definition pair_recur A B C f (p : A * B) : C := f (fst p) (snd p).

    Definition map_find A f (m : LabelMap.t A) : option (label * A) :=
      List.find (pair_recur f) (LabelMap.elements m).

    Definition find_by_word A (m : LabelMap.t A) (p : W) :=
      match map_find (fun lbl _ => is_label_map_to_word lbl p) m with
        | Some (_, a) => Some a
        | None => None
      end.

    Definition is_export := find_by_word exports.

    Definition is_import := find_by_word imports.

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

  Section module.

      Variable m : GoodModule.

      Section f.

        Variable f : GoodFunction.

        Section body.
          
          Variable im : LabelMap.LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Definition mod_name := MName m.

          Require Import NameDecoration.
          Definition tgt := ((impl_module_name mod_name)!(FName f))%SP.

          Require Import AutoSep.
          Definition body := 
            @Seq_ _ im_g mod_name
                 (AssertStar_ im mod_name accessible_labels (spec f))
                 (Goto_ im_g mod_name tgt).

        End body.

        Require Import StructuredModule.
        Definition make_stub : function (GoodModule.Name m) :=
          (FName f, spec_without_funcs_ok f fs, body).

      End f.

      Require Import Inv.

      Definition foreign_spec spec : assert := 
        st ~> ExX, Inv.foreign_spec _ spec st.

      Definition bimports : list import := 
        List.map 
          (fun (p : label * ForeignFuncSpec) => 
             let (lbl, spec) := p in
             (fst lbl, snd lbl, foreign_spec spec)) 
          (LabelMap.elements imports) 
          ++
          List.map 
          (fun (p : label * InternalFuncSpec) =>
             let (lbl, spec) := p in
             (impl_module_name (fst lbl), snd lbl, CompileFuncSpec.spec spec))
          (LabelMap.elements exports).
          

      Definition stubs := map make_stub (Functions m).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Require Import LabelMap.

      Lemma good_vcs : forall ls, vcs (makeVcs bimports stubs (map make_stub ls)).
        induction ls; simpl; eauto.
        Require Import Wrap.
        Opaque funcs_ok.
        Opaque spec_without_funcs_ok.
        wrap0.
        descend.
        instantiate (1 := fs).

        2 : eauto.

        Focus 2.
        replace (LabelMap.find (elt:=assert) (tgt a) (fullImports bimports stubs)) with (Some (spec a)) by admit.
        eauto.

        Transparent funcs_ok.
        Transparent spec_without_funcs_ok.
        unfold funcs_ok.
        post; descend.

        apply injL; intro.
        Opaque internal_spec.
        post; descend.
        instantiate (1 := spec_without_funcs_ok x1 fs).
        admit.
        unfold spec_without_funcs_ok at 2.
        step auto_ext.
        Transparent internal_spec.
        step auto_ext.
        rewrite sepFormula_eq; apply Imply_refl.

        apply injL; intro.
        Opaque Inv.foreign_spec.
        post; descend.
        instantiate (1 := foreign_spec x1).
        admit.
        unfold foreign_spec.
        step auto_ext.
        Transparent Inv.foreign_spec.
        step auto_ext.
        rewrite sepFormula_eq; apply Imply_refl.
      Qed.

      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        admit.
        admit.
        eapply good_vcs.
      Qed.

  End module.

  Definition ms := map make_module modules.

  Definition empty_module := @StructuredModule.bmodule_ nil "empty_module" nil.

  Fixpoint link_all ls := 
    match ls with
      | nil => empty_module
      | x :: nil => x
      | x :: xs => link x (link_all xs)
    end.

  Definition m := link_all ms.

  Theorem ok : moduleOk m.
    admit.
  Qed.

End TopSection.
