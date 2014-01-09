Set Implicit Arguments.

Section TopSection.

  Require Import SyntaxModule.
  Variable modules : list CitoModule.

  Require Import Semantics.
  Require Import CompileFuncSpec.
  Definition fs : settings -> W -> option Callee.
    admit.
  Defined.

  Definition stub_mod_name s := ("stub_" ++ s)%string.

  Section f.

    Variable f : Func.

    Require Import Malloc.
    Require Import Safe.
    Require Import SyntaxFunc.
    Definition spec f : assert := 
      st ~> Ex fs, 
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

  Definition imports : list import.
    admit.
  Qed.

  Definition m := StructuredModule.bmodule_ imports stubs.

  Theorem ok : XCAP.moduleOk m.
  Qed.

End TopSection.
