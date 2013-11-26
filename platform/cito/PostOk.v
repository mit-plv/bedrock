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

  Lemma post_ok : 
    forall (pre : assert) (specs : codeSpec W (settings * state))
           (x : settings * state),
      vcs (verifCond layout vars temp_size s k pre) ->
      interp specs
             (Postcondition
                (compile layout vars temp_size imports_global modName s k pre) x) ->
      interp specs (postcond layout vars temp_size k x).
  Proof.
    unfold verifCond, imply; induction s.

    (* skip *)
    wrap0.
    unfold_eval; repeat (first [do_wrap | do_unfold_eval | eval_step auto_ext]).
    discharge_fs; descend; try clear_imports; repeat hiding ltac:(step auto_ext); eauto.

    admit.
  Qed.

End TopSection.