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
  Require Import Wrap.

  Definition compile := compile layout vars temp_size imports_global modName.

  Require Import Semantics.
  Require Import Safe.
  Require Import Notations.
  Require Import SemanticsFacts.
  Require Import ScopeFacts.
  Require Import ListFacts.
  Require Import StringSet.
  Require Import SetFacts.
  Require Import CompileStmtTactics.

  Open Scope stmt.

  Opaque funcs_ok.
  Opaque mult.
  Opaque star. (* necessary to use eapply_cancel *)

  Hint Resolve Subset_in_scope_In.
  Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).
  Hint Resolve map_length.

  Set Printing Coercions.

  Require Import SemanticsExpr.
  Require Import SepHints.
  Require Import GeneralTactics.
  Require Import WordFacts.
  Require Import Arith.
  Require Import InvFacts.
  Require Import VerifCondOkTactics.

  Open Scope nat.

  Lemma verifCond_ok : 
    forall s k (pre : assert),
      vcs (verifCond layout vars temp_size s k pre) ->
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

  Qed.

End TopSection.