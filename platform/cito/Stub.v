Require Import CompileFuncSpec.

Set Implicit Arguments.

Require Import Label.
Definition to_lbl (l : label) : Labels.label := (fst l, Global (snd l)).
Coercion to_lbl : label >-> Labels.label.

Section TopSection.

  Require Import GoodModule.
  Variable modules : list GoodModule.

  Require Import Semantics.
  Variable imports : LabelMap.t ForeignFuncSpec.

  Require Import GoodFunction.
  Definition to_internal_func_spec (f : GoodFunction) : InternalFuncSpec :=
    {|
      Semantics.ArgVars := ArgVars f;
      Semantics.ArgVarsGood := NoDupArgVars f;
      Semantics.RetVar := RetVar f;
      Semantics.Body := Body f
    |}.

  Fixpoint flatten A (ls : list (list A)) :=
    match ls with
      | nil => nil
      | x :: xs => x ++ flatten xs
    end.

  Definition to_map B ls :=
    List.fold_left
      (fun m p => LabelMap.add (fst p) (snd p) m)
      ls (LabelMap.empty B).

  Definition exports : LabelMap.t InternalFuncSpec :=
    to_map
      (flatten 
         (List.map 
            (fun m =>
               List.map 
                 (fun f =>
                    ((GoodModule.Name m, GoodFunction.Name f), to_internal_func_spec f)
                 ) (Functions m)
            ) modules)).

  Section fs.

    Variable stn : settings.

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

    Lemma fs_funcs_ok : forall specs, interp specs (Inv.funcs_ok stn fs).
      admit.
    Qed.

  End fs.

  Section module.

      Variable m : GoodModule.

      Section f.

        Variable f : GoodFunction.

        Require Import Malloc.
        Require Import Safe.
        Definition spec : assert := 
          st ~> 
             let stn := fst st in
             CompileFuncSpec.inv' (ArgVars f) (Body f) (RetVar f) (fs stn) st.

(*          st ~> 
             let stn := fst st in
             let env := (Labels stn, fs stn) in
             let vars := ArgVars f in
             let s := Body f in
             let ret_var := RetVar f in
             ExX, Ex v, Ex e_stack,
             ![^[is_state st#Sp e_stack e_stack vars v * mallocHeap 0] * #0] st /\
             [| Safe env s v |] /\
             (st#Rp, stn) 
               @@@ (
                 st' ~> Ex v', Ex e_stack',
                 ![^[is_state st'#Sp e_stack' e_stack vars v' * mallocHeap 0] * #1] st' /\
                 [| RunsTo env s v v' /\
                    st'#Sp = st#Sp /\
                    st'#Rv = sel (fst v') ret_var |]).*)

        Section body.
          
          Variable im : LabelMap.LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Require Import NameDecoration.
          Definition tgt := ((impl_module_name (GoodModule.Name m))!(Name f))%SP.

          Definition body := Goto_ im_g (GoodModule.Name m) tgt.

        End body.

        Require Import StructuredModule.
        Definition make_stub : function (GoodModule.Name m) :=
          (Name f, spec, body).

      End f.

      Definition to_func (spec : InternalFuncSpec) : SyntaxFunc.Func :=
        {|
          SyntaxFunc.Name := "";
          SyntaxFunc.ArgVars := Semantics.ArgVars spec;
          SyntaxFunc.RetVar := Semantics.RetVar spec;
          SyntaxFunc.Body := Semantics.Body spec
        |}.

      Definition spec_internal (spec : InternalFuncSpec) : assert :=
        CompileFuncSpec.inv (Semantics.ArgVars spec) (Semantics.Body spec) (Semantics.RetVar spec).

      Require Import Inv.
      Definition spec_foreign (spec : ForeignFuncSpec) : assert := 
        (st ~> ExX, Ex pairs, Ex rp, Ex e_stack,
         let stn := fst st in
         let heap := make_heap pairs in
         ![^[is_state st#Sp rp e_stack nil (empty_vs, heap) (map fst pairs) * mallocHeap 0] * #0] st /\
         [| disjoint_ptrs pairs /\
            PreCond spec (map snd pairs) |] /\
         (st#Rp, stn) 
           @@@ (
             st' ~> Ex args', Ex addr, Ex ret, Ex rp', Ex outs,
             let t := decide_ret addr ret in
             let ret_w := fst t in
             let ret_a := snd t in
             let triples := make_triples pairs outs in
             let heap := fold_left store_out triples heap in
             ![^[is_state st#Sp rp' e_stack nil (empty_vs, heap) args' * layout_option ret_w ret_a * mallocHeap 0] * #1] st' /\
             [| length outs = length pairs /\
                PostCond spec (map (fun x => (ADTIn x, ADTOut x)) triples) ret /\
                length args' = length triples /\
                st'#Rv = ret_w /\
                st'#Sp = st#Sp |]))%PropX.

      Definition bimports : list import := 
        List.map 
          (fun (p : label * ForeignFuncSpec) => 
             let (lbl, spec) := p in
             (fst lbl, snd lbl, spec_foreign spec)) 
          (LabelMap.elements imports) 
          ++
          List.map 
          (fun (p : label * InternalFuncSpec) =>
             let (lbl, spec) := p in
             (impl_module_name (fst lbl), snd lbl, spec_internal spec))
          (LabelMap.elements exports).
          

      Definition stubs := map make_stub (Functions m).

      Definition make_module := StructuredModule.bmodule_ bimports stubs.

      Lemma good_vcs : forall ls, vcs (makeVcs bimports stubs (map make_stub ls)).
        induction ls; simpl; eauto.
        Require Import Wrap.
        wrap0.
        Require Import LabelMap.
        replace (LabelMap.find (elt:=assert) (tgt a) (fullImports bimports stubs)) with (Some (spec_internal (to_internal_func_spec a))).
        unfold spec.
        unfold spec_internal.
        unfold to_internal_func_spec; simpl.
        unfold CompileFuncSpec.inv.
        intros.
        destruct stn_st.
        simpl in *.
        Opaque funcs_ok.
        Opaque inv'.
        step auto_ext.
        descend.
        instantiate (1 := fs s).
        eapply fs_funcs_ok.
        eauto.
        admit.
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
