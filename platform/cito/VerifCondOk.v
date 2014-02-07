Require Import CompileStmtSpec CompileStmtImpl.

Set Implicit Arguments.

Module Make (Import M : RepInv.RepInv).

  Require Import VerifCondOkNonCall.
  Module Import VerifCondOkNonCallMake := VerifCondOkNonCall.Make M.
  Require Import VerifCondOkNonCall2.
  Module Import VerifCondOkNonCall2Make := VerifCondOkNonCall2.Make M.
  Require Import VerifCondOkCall.
  Module Import VerifCondOkCallMake := VerifCondOkCall.Make M.
  Module Import CompileStmtImplMake := CompileStmtImpl.Make M.
  Module Import CompileStmtSpecMake := CompileStmtSpec.Make M.
  Module Import InvMake := Inv.Make M.

  Section TopSection.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Variable rv_postcond : W -> Semantics.State -> Prop.

    Notation do_compile := (CompileStmtImplMake.compile vars temp_size rv_postcond imports_global modName).

    Lemma verifCond_ok : 
      forall s k (pre : assert),
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply; induction s.

      eapply verifCond_ok_skip; eauto.
      eapply verifCond_ok_seq; eauto.
      eapply verifCond_ok_if; eauto.
      eapply verifCond_ok_while; eauto.

      eapply verifCond_ok; eauto.

      eapply verifCond_ok_label; eauto.
      eapply verifCond_ok_assign; eauto.

    Qed.

  End TopSection.

End Make.