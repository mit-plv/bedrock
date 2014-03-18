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
  
    Definition strengthen_op_ax (spec_op : InternalFuncSpec) spec_ax env_ax :=
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
        TransitSafe spec_ax (map (sel (fst v)) args) (snd v) ->
        TransitTo spec_ax (map (sel (fst v)) args) (snd v) (sel (fst v') rvar) (snd v').

    Definition strengthen (env_op env_ax : Env) := 
      (forall lbl, fst env_op lbl = fst env_ax lbl) /\ 
      let fs_op := snd env_op in
      let fs_ax := snd env_ax in
      forall w,
        fs_op w = fs_ax w \/
        exists spec_op spec_ax,
          fs_op w = Some (Internal spec_op) /\
          fs_ax w = Some (Foreign spec_ax) /\
          strengthen_op_ax spec_op spec_ax env_ax.

    Hint Unfold RunsTo.
    Hint Constructors Semantics.RunsTo.
    Hint Unfold Safe.
    Hint Constructors Semantics.Safe.

    Require Import GeneralTactics GeneralTactics3.

    Lemma strengthen_runsto : forall env_op s v v', RunsTo env_op s v v' -> forall env_ax, strengthen env_op env_ax -> Safe env_ax s v -> RunsTo env_ax s v v'.
      induction 1; simpl; intros; unfold_all.

      Focus 7.
      (* call internal *)
      generalize H2; intro.
      unfold strengthen, strengthen_op_ax in H2; openhyp.
      destruct (H5 (eval (fst v) f)); clear H5.

      eapply RunsToCallInternal; eauto.
      destruct env_ax; destruct env_op; simpl in *.
      congruence.
      eapply IHRunsTo; eauto.

      destruct env_ax; destruct env_op; simpl in *.
      inv_clear H3; simpl in *.
      rewrite H6 in H.
      rewrite H9 in H; injection H; intros; subst.
      eapply H12.
      eauto.
      rewrite H6 in H.
      rewrite H9 in H; discriminate.

      openhyp.
      destruct env_ax; destruct env_op; simpl in *.
      rewrite H in H5; injection H5; intros; subst.
      eapply IHRunsTo in H4.
      eapply H9 in H4; clear H9.
      simpl in *.
      eapply TransitTo_RunsTo; eauto.
      simpl in *.
      rewrite <- H0.
      eauto.
      simpl.
      eauto.

      simpl in *.
      rewrite H0.
      eapply Safe_TransitSafe.
      instantiate (2 := (_, _)).
      simpl.
      eauto.
      eauto.
      eapply H8.
      simpl.
      rewrite H0.
      eapply Safe_TransitSafe.
      instantiate (2 := (_, _)).
      simpl.
      eauto.
      eauto.

      Focus 7.
      (* call foreign *)
      generalize H6; intro.
      unfold strengthen, strengthen_op_ax in H6; openhyp.
      destruct (H9 (eval (fst v) f)); clear H9.
      eapply RunsToCallForeign; eauto.
      destruct env_ax; destruct env_op; simpl in *.
      congruence.

      openhyp.
      destruct env_ax; destruct env_op; simpl in *.
      rewrite H in H9; discriminate.

      (* skip *)
      eauto.

      (* seq *)
      inv_clear H2.
      econstructor; eauto.
      eapply IHRunsTo1; eauto.
      eapply IHRunsTo2; eauto.
      eapply H7; eapply IHRunsTo1; eauto.

      (* if true *)
      inv_clear H2.
      openhyp.
      eapply RunsToIfTrue; eauto.
      eapply IHRunsTo; eauto.
      rewrite H2 in H; discriminate.

      (* if false *)
      inv_clear H2.
      openhyp.
      rewrite H2 in H; discriminate.
      eapply RunsToIfFalse; eauto.
      eapply IHRunsTo; eauto.

      (* while true *)
      inv_clear H3.
      eapply RunsToWhileTrue; eauto.
      eapply IHRunsTo1; eauto.
      eapply IHRunsTo2; eauto.
      eapply H9; eapply IHRunsTo1; eauto.
      rewrite H7 in H; discriminate.
      
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
      unfold strengthen, strengthen_op_ax in H0; openhyp.
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
      unfold strengthen, strengthen_op_ax in H0; openhyp.
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