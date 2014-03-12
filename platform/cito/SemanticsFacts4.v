Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import AutoSep.

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
          (forall pairs, 
             PreCond spec_ax (map snd pairs) ->
             length args = length pairs /\
             (forall v,
                let vs := fst v in
                let heap := snd v in
                map (sel vs) args = map fst pairs ->
                good_inputs heap pairs ->
                Safe env_ax s v)) /\
          forall v v', 
            RunsTo env_ax s v v' -> 
            exists triples addr ret,
              let vs := fst v in
              let heap := snd v in
              map (sel vs) args = map (@Word _) triples /\
              good_inputs heap (map (fun x => (Word x, ADTIn x)) triples) /\
              PreCond spec_ax (map (@ADTIn _) triples) /\
              PostCond spec_ax (map (fun x => (ADTIn x, ADTOut x)) triples) ret /\
              let heap := fold_left store_out triples heap in
              let t := decide_ret addr ret in
              let ret_w := fst t in
              let ret_a := snd t in
              separated heap ret_w ret_a /\
              let heap := heap_upd_option heap ret_w ret_a in
              snd v' = heap /\
              sel (fst v') rvar = ret_w.

    Ltac unfold_all :=
      repeat match goal with
               | H := _ |- _ => unfold H in *; clear H
             end.

    Hint Unfold RunsTo.
    Hint Constructors Semantics.RunsTo.
    Hint Unfold Safe.
    Hint Constructors Semantics.Safe.

    Lemma strengthen_runsto : forall env_op s v v', RunsTo env_op s v v' -> forall env_ax, strengthen env_op env_ax -> RunsTo env_ax s v v'.
      induction 1; simpl; intros; unfold_all.

      Focus 7.
      (* call internal *)
      generalize H2; intro.
      Require Import GeneralTactics.
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
      eapply H7 in H3; clear H7.
      openhyp.
      simpl in *.
      subst.
      rewrite H12.
      eapply RunsToCallForeign; eauto.
      congruence.

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
      eapply H6; simpl; eauto.
      rewrite H10.
      eauto.
      eapply f_equal with (f := @length _) in H5.
      repeat rewrite map_length in *.
      rewrite H5.
      eapply H6; eauto.
      
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