Set Implicit Arguments.

Require Import Compile.

Require Import Facade.
Require Import Memory IL.
Require Import GLabel.

Require Import String.
Local Open Scope string_scope.
Require Import StringMap.
Import StringMap.
Require Import StringMapFacts.
Import FMapNotations.
Local Open Scope fmap_scope.
Require Import List.
Require Import ListFacts ListFacts2 ListFacts3 ListFactsNew ListFacts4.
Local Open Scope list_scope.
Require Import GeneralTactics GeneralTactics2 GeneralTactics3 GeneralTactics4.

Section ADTValue.

  Variable ADTValue : Type.

  Notation RunsTo := (@RunsTo ADTValue).
  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).
  Notation Adt := (@ADT ADTValue).

  Section Safe_coind.

    Variable env : Env.

    Variable R : Stmt -> State -> Prop.

    Hypothesis SeqCase : forall a b st, R (Seq a b) st -> R a st /\ forall st', RunsTo env a st st' -> R b st'.

    Hypothesis IfCase : forall cond t f st, R (If cond t f) st -> (is_true st cond /\ R t st) \/ (is_false st cond /\ R f st).

    Hypothesis WhileCase : 
      forall cond body st, 
        let loop := While cond body in 
        R loop st -> 
        (is_true st cond /\ R body st /\ (forall st', RunsTo env body st st' -> R loop st')) \/ 
        (is_false st cond).

    Hypothesis AssignCase :
      forall x e st,
        R (Facade.Assign x e) st ->
        not_mapsto_adt x st = true /\
        exists w, eval st e = Some (Sca w).

    Hypothesis LabelCase : 
      forall x lbl st,
        R (Label x lbl) st -> 
        not_mapsto_adt x st = true /\
        exists w, Label2Word env lbl = Some w.

    Hypothesis CallCase : 
      forall x f args st,
        R (Call x f args) st ->
        NoDup args /\
        not_mapsto_adt x st = true /\
        exists f_w input, 
          eval st f = Some (Sca f_w) /\
          mapM (sel st) args = Some input /\
          ((exists spec,
              Word2Spec env f_w = Some (Axiomatic spec) /\
              PreCond spec input) \/
           (exists spec,
              Word2Spec env f_w = Some (Operational _ spec) /\
              length args = length (ArgVars spec) /\
              let callee_st := make_map (ArgVars spec) input in
              R (Body spec) callee_st /\
              (forall callee_st',
                 RunsTo env (Body spec) callee_st callee_st' ->
                 sel callee_st' (RetVar spec) <> None /\
                 no_adt_leak input (ArgVars spec) (RetVar spec) callee_st'))).
    
    Hint Constructors Safe.

    Require Import GeneralTactics.

    Theorem Safe_coind : forall c st, R c st -> Safe env c st.
      cofix; intros; destruct c.

      solve [eauto].
      Guarded.

      solve [eapply SeqCase in H; openhyp; eapply SafeSeq; eauto].
      Guarded.

      solve [eapply IfCase in H; openhyp; eauto].
      Guarded.

      solve [eapply WhileCase in H; openhyp; eauto].
      Guarded.

      solve [eapply CallCase in H; openhyp; simpl in *; intuition eauto].
      Guarded.

      solve [eapply LabelCase in H; openhyp; eauto].
      Guarded.

      solve [eapply AssignCase in H; openhyp; eauto].
    Qed.

  End Safe_coind.
  
  
  Require Import WordMap.
  Import WordMap.
  Require Import WordMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Require Import FacadeFacts.

  Notation CitoSafe := (@Semantics.Safe ADTValue).

  Ltac try_eexists := try match goal with | |- exists _, _ => eexists end.
  Ltac try_split := try match goal with | |- _ /\ _ => split end.
  Ltac pick_related := try match goal with | |- related _ _ => eauto end.

  Theorem compile_safe :
    forall s_env s s_st,
      Safe s_env s s_st ->
      (* h1 : the heap portion that this program is allowed to change *)
      forall vs h h1, 
        h1 <= h -> 
        related s_st (vs, h1) -> 
        let t_env := compile_env s_env in
        let t := compile s in
        let t_st := (vs, h) in
        CitoSafe t_env t t_st.
  Proof.
    simpl; intros.
    eapply 
      (Semantics.Safe_coind 
         (fun t v =>
            exists s s_st h1,
              let vs := fst v in
              let h := snd v in
              Safe s_env s s_st /\
              h1 <= h /\
              related s_st (vs, h1) /\
              t = compile s)
      ); [ .. | repeat try_eexists; simpl in *; intuition eauto ]; clear; simpl; intros until v; destruct v as [vs h]; intros [s [s_st [h1 [Hsf [Hsm [Hr Hcomp]]]]]]; destruct s; simpl in *; try discriminate; inject Hcomp.

    (* seq *)
    {
      rename s1 into a.
      rename s2 into b.
      inversion Hsf; subst.
      destruct H2 as [Hsfa Hsfb].
      split.
      - exists a, s_st, h1; eauto.
      - intros [vs' h'] Hcrt; simpl in *.
        eapply compile_runsto in Hcrt; eauto.
        simpl in *.
        openhyp.
        repeat try_eexists; repeat try_split; pick_related; eauto.
        eapply diff_submap.
    }

    (* if *)
    {
      rename e into cond.
      rename s1 into t.
      rename s2 into f.
      inversion Hsf; subst.
      - left.
        rename H3 into Hcond.
        rename H4 into Hsfbr.
        split.
        + eapply eval_bool_wneb; eauto.
        + repeat try_eexists; repeat try_split; pick_related; eauto.
      - right.
        rename H3 into Hcond.
        rename H4 into Hsfbr.
        split.
        + eapply eval_bool_wneb; eauto.
        + repeat try_eexists; repeat try_split; pick_related; eauto.
    }

    (* while *)
    {
      rename e into cond.
      rename s into body.
      inversion Hsf; unfold_all; subst.
      - left.
        rename H1 into Hcond.
        rename H2 into Hsfbody.
        rename H4 into Hsfk.
        repeat try_split.
        + eapply eval_bool_wneb; eauto.
        + repeat try_eexists; repeat try_split; pick_related; eauto.
        + intros [vs' h'] Hcrt; simpl in *.
          eapply compile_runsto in Hcrt; eauto.
          simpl in *.
          openhyp.
          repeat try_eexists; repeat try_split; pick_related; eauto.
          eapply diff_submap.
      - right.
        eapply eval_bool_wneb; eauto.
    }

    (* call *)
    {
      rename s into x.
      rename e into f_e.
      rename l into args.
      inversion Hsf; unfold_all; subst.
      (* axiomatic *)
      {
        right.
        (*here*)
      }
    }      

    (* label *)
    {
      rename s into x.
      rename g into lbl.
      inversion Hsf; unfold_all; subst.
      intuition.
    }

  Qed.

End ADTValue.