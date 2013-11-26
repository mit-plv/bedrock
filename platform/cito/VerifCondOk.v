Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Section TopSection.

  Require Import Inv.

  Variable layout : Layout.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Require Import Syntax.

  Variable s k : Stmt.

  Require Import Wrap.

  Lemma verifCond_ok : 
    forall pre : assert,
      vcs (verifCond layout vars temp_size s k pre) ->
      vcs
        (VerifCond (compile layout vars temp_size imports_global modName s k pre)).
    admit.
  Qed.

End TopSection.