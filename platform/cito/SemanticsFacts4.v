Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import AutoSep.

  Require Import Transit.
  Module Import TransitMake := Make E.
  Require Import Semantics.
  Module Import SemanticsMake := Make E.

  Section TopSection.

    Require Import Syntax.
    Require Import GLabel.

    Definition Env := ((glabel -> option W) * (W -> option Callee))%type.

    Require Import SemanticsExpr.
  
    Definition strengthen (env_op env_ax : Env) := 
      (forall lbl, fst env_op lbl = fst env_ax lbl) /\ 
      let fs_op := snd env_op in
      let fs_ax := snd env_ax in
      forall w,
        fs_op w = fs_ax w \/
        exists spec_op spec_ax,
          fs_op w = Some (Internal spec_op) /\
          fs_ax w = Some (Foreign spec_ax) /\
          let args := ArgVars spec_op in
          let rvar := RetVar spec_op in
          let s := Body spec_op in
          (forall ins, 
             PreCond spec_ax ins ->
             length args = length ins) /\
          (forall v,
             TransitSafe spec_ax (map (sel (fst v)) args) (snd v) ->
             Safe env_ax s v) /\
          forall v v', 
            RunsTo env_ax s v v' -> 
            TransitTo spec_ax (map (sel (fst v)) args) (snd v) (sel (fst v') rvar) (snd v').

    Hint Unfold RunsTo.
    Hint Constructors Semantics.RunsTo.
    Hint Unfold Safe.
    Hint Constructors Semantics.Safe.

    Require Import GeneralTactics GeneralTactics3.

    Lemma strengthen_runsto : forall env_op s v v', RunsTo env_op s v v' -> forall env_ax, strengthen env_op env_ax -> RunsTo env_ax s v v'.
      induction 1; simpl; intros; unfold_all.

      Focus 7.
      (* call internal *)
      generalize H2; intro.
      unfold strengthen in H2; openhyp.
      destruct (H4 (eval (fst v) f)); clear H4.

      eapply RunsToCallInternal; eauto.
      destruct env_ax; destruct env_op; simpl in *.
      congruence.
      eapply IHRunsTo; eauto.

      openhyp.
      destruct env_ax; destruct env_op; simpl in *.
      rewrite H in H4; injection H4; intros; subst.
      eapply IHRunsTo in H3.
      eapply H8 in H3; clear H8.
      simpl in *.
      eapply TransitTo_RunsTo; eauto.
      simpl in *.
      rewrite <- H0.
      eauto.
      simpl.
      eauto.

      Focus 7.
      (* call foreign *)
      generalize H5; intro.
      unfold strengthen in H5; openhyp.
      destruct (H7 (eval (fst v) f)); clear H7.
      eapply RunsToCallForeign; eauto.
      destruct env_ax; destruct env_op; simpl in *.
      congruence.

      openhyp.
      destruct env_ax; destruct env_op; simpl in *.
      rewrite H in H7; discriminate.

      (* skip *)
      eauto.

      (* seq *)
      econstructor; eauto.
      eapply IHRunsTo1; eauto.
      eapply IHRunsTo2; eauto.

      (* if true *)
      eapply RunsToIfTrue; eauto.
      eapply IHRunsTo; eauto.

      (* if false *)
      eapply RunsToIfFalse; eauto.
      eapply IHRunsTo; eauto.

      (* while true *)
      eapply RunsToWhileTrue; eauto.
      eapply IHRunsTo1; eauto.
      eapply IHRunsTo2; eauto.

      (* while false *)
      eauto.

      (* label *)
      econstructor.
      destruct H0.
      rewrite <- H0.
      eauto.

      (* assign *)
      eauto.
    Qed.

    Lemma strengthen_safe : forall env_ax s v, Safe env_ax s v -> forall env_op, strengthen env_op env_ax -> Safe env_op s v.
      intros.
      eapply (Safe_coind (fun s v => Safe env_ax s v)); [ .. | eauto ]; generalize H0; clear; intros.

      Focus 4.
      inversion H; unfold_all; subst; simpl in *.
      (* call internal *)
      generalize H0; intro.
      unfold strengthen in H0; openhyp.
      destruct (H2 (eval (fst v) f)); clear H2.
      left; descend; eauto.
      destruct env_ax; destruct env_op; simpl in *.
      rewrite H3; eauto.

      openhyp.
      destruct env_ax; destruct env_op; simpl in *.
      destruct v; simpl in *.
      rewrite H4 in H3; discriminate.

      (* call foreign *)
      generalize H0; intro.
      unfold strengthen in H0; openhyp.
      destruct (H2 (eval (fst v) f)); clear H2.
      right; descend; eauto.
      destruct env_ax; destruct env_op; simpl in *.
      rewrite H3; eauto.

      openhyp.
      destruct env_ax; destruct env_op; simpl in *.
      destruct v; simpl in *.
      rewrite H4 in H3; injection H3; intros; subst.
      left; descend; eauto.
      Focus 2.
      eapply H9; simpl; eauto.
      rewrite H11.
      unfold TransitSafe.
      descend; eauto.
      erewrite H6; eauto.
      eapply f_equal with (f := @length _) in H5.
      repeat rewrite map_length in *.
      eauto.
      
      (* seq *)
      inversion H; unfold_all; subst.
      descend; eauto.
      eapply H5; eauto.
      eapply strengthen_runsto; eauto.

      (* if *)
      inversion H; unfold_all; subst.
      eauto.

      (* while *)
      unfold_all.
      inversion H; unfold_all; subst.
      left; descend; eauto.
      eapply H6; eauto.
      eapply strengthen_runsto; eauto.

      right; eauto.

      (* label *)
      inversion H; unfold_all; subst.
      destruct H0.
      rewrite H0; eauto.

    Qed.

  End TopSection.

End Make.