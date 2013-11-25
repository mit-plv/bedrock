Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Section Compile.

  Require Import Inv.

  Variable layout : Layout.

  Variable vars temp_vars : list string.

  Require Import GoodVars.

  Hypothesis h_good_vars : good_vars vars temp_vars.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Require Import Syntax.

  Variable s k : Stmt.

  Require Import Wrap.

  Definition compile : cmd imports modName.
    refine (
        Wrap imports imports_global modName 
             (CompileStmtImpl.compile layout vars temp_vars imports_global modName s k) 
             (fun _ => postcond layout vars temp_vars k) 
             (verifCond layout vars temp_vars s k) 
             _ _).
    Require Import PostOk VerifCondOk.
    eapply post_ok.
    eapply verifCond_ok.
  Defined.

End Compile.