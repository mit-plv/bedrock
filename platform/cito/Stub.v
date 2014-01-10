Require Import CompileFuncSpec.

Set Implicit Arguments.

Section TopSection.

  Require Import SyntaxModule.
  Variable modules : list CitoModule.

  Require Import Semantics.
  Variable imports : LabelMap.t ForeignFuncSpec.

  Definition stub_mod_name s := ("stub_" ++ s)%string.

  Definition make_stub_label (lbl : label) : label := (stub_mod_name (fst lbl), snd lbl).

  Definition exports_real : LabelMap.t InternalFuncSpec.
    admit.
  Qed.

  Section env.

    Variable stn : settings.

    Definition labels (lbl : label) : option W :=
      if LabelMap.mem lbl exports_real then
        Labels stn (make_stub_label lbl)
      else
        Labels stn lbl.

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

    Definition find_f A f (m : LabelMap.t A) : option (label * A) :=
      List.find (pair_recur f) (LabelMap.elements m).

    Definition find_by_word A (m : LabelMap.t A) (p : W) :=
      match find_f (fun lbl _ => is_label_map_to_word lbl p) m with
        | Some (_, a) => Some a
        | None => None
      end.

    Definition is_export := find_by_word exports_real.

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

  End env.

  Section f.

    Variable f : Func.

    Require Import Malloc.
    Require Import Safe.
    Require Import SyntaxFunc.
    Definition spec f : assert := 
      st ~> 
      let stn := fst st in
      let env := (labels stn, fs stn) in
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
             st'#Rv = sel (fst v') ret_var |]).

    Section body.
      
      Variable m : CitoModule.

      Variable im : LabelMap.t assert.

      Variable im_g : importsGlobal im.

      Definition tgt := ((ModuleName m)!(Name f))%SP.

      Definition body := Goto_ im_g (stub_mod_name ((ModuleName m))) tgt.

    End body.

    Require Import StructuredModule.
    Definition make_stub m : function (stub_mod_name (ModuleName m)) :=
      (Name f, spec f, body m).

  End f.

  Definition spec_foreign : ForeignFuncSpec -> assert.
    admit.
  Qed.

  Definition get_func_name : label -> string.
    admit.
  Qed.

  Definition bimports : list import := 
    List.map 
      (fun (p : label * ForeignFuncSpec) => 
         let (lbl, spec) := p in
         (fst lbl, get_func_name lbl, spec_foreign spec)) 
      (LabelMap.elements imports).

  (* todo: changed label to string*string, or add importsGlobal hypothesis *)
  (* todo: put all stubs under one module *)

  Definition m := StructuredModule.bmodule_ imports stubs.

  Theorem ok : XCAP.moduleOk m.
  Qed.

End TopSection.
