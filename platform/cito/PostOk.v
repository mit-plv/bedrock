Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Section TopSection.

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

  Lemma post_ok : forall (pre : assert) (specs : codeSpec W (settings * state))
         (x : settings * state),
    vcs (verifCond layout vars temp_vars s k pre) ->
    interp specs
           (Postcondition
              (compile layout vars temp_vars imports_global modName s k pre) x) ->
    interp specs (postcond layout vars temp_vars k x).
    admit.
  Qed.

End TopSection.