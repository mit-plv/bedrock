Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Section Compile.

  Require Import Inv.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Require Import Syntax.

  Variable s k : Stmt.

  Require Import Wrap.

  Definition compile : cmd imports modName.
    refine (
        Wrap imports imports_global modName 
             (CompileStmtImpl.compile vars temp_size imports_global modName s k) 
             (fun _ => postcond vars temp_size k) 
             (verifCond vars temp_size s k) 
             _ _).
    Require Import PostOk VerifCondOk.
    eapply post_ok.
    eapply verifCond_ok.
  Defined.

End Compile.