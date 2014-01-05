Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Section TopSection.

  Require Import Inv.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Variable rv_postcond : W -> Semantics.State -> Prop.

  Definition compile := compile vars temp_size imports_global modName rv_postcond.

  Lemma verifCond_ok : 
    forall s k (pre : assert),
      vcs (verifCond vars temp_size s k rv_postcond pre) ->
      vcs
        (VerifCond (compile s k pre)).
  Proof.

    unfold verifCond, imply; induction s.

    Require Import VerifCondOkNonCall.

    eapply verifCond_ok_skip; eauto.
    eapply verifCond_ok_seq; eauto.
    eapply verifCond_ok_if; eauto.
    eapply verifCond_ok_while; eauto.

    Require Import VerifCondOkCall.
    eapply verifCond_ok; eauto.

    Require Import VerifCondOkNonCall2.
    eapply verifCond_ok_label; eauto.
    eapply verifCond_ok_assign; eauto.

  Qed.

End TopSection.