(** This file implements symbolic evaluation for the
 ** language defined in IL.v
 **)
Require Import IL SepIL.
Require Import Word Memory.
Require Import DepList EqdepClass.
Require Import PropX.
Require Import SepExpr SymEval.
Require Import Expr.
Require Import Prover.
Require Import Env TypedPackage.
Import List.

Require Structured SymEval.
Require Import ILEnv SymIL.

Set Implicit Arguments.
Set Strict Implicit.

(** The Symbolic Evaluation Interfaces *)
Module MEVAL := SymIL.MEVAL.

Module SymIL_Correct.
  Section typed.
    Variable ts : list type.
    Let types := repr bedrock_types_r ts.

    Local Notation "'pcT'" := tvWord.
    Local Notation "'stT'" := (tvType 0).
    Local Notation "'tvState'" := (tvType 1).
    Local Notation "'tvTest'" := (tvType 2).
    Local Notation "'tvReg'" := (tvType 3).

    Variable fs : functions types.
    Let funcs := repr (bedrock_funcs_r ts) fs.
    Variable preds : SEP.predicates types pcT stT.

    Variable Prover : ProverT types.
    Variable PC : ProverT_correct Prover funcs.

    Variable meval : MEVAL.MemEvaluator types pcT stT.
    Variable meval_correct : MEVAL.MemEvaluator_correct meval funcs preds tvWord tvWord
      (@IL_mem_satisfies ts) (@IL_ReadWord ts) (@IL_WriteWord ts).

    Variable facts : Facts Prover.
    Variable meta_env : env types.
    Variable vars_env : env types.

    Ltac t_correct := 
      simpl; intros;
        unfold IL_stn_st, IL_mem_satisfies, IL_ReadWord, IL_WriteWord in *;
          repeat (simpl in *; 
            match goal with
              | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
              | [ H : prod _ _ |- _ ] => destruct H
              | [ H : match ?X with 
                        | Some _ => _
                        | None => _ 
                      end |- _ ] =>
              revert H; case_eq X; intros; try contradiction
              | [ H : match ?X with 
                        | Some _ => _
                        | None => _ 
                      end = _ |- _ ] =>
              revert H; case_eq X; intros; try congruence
              | [ H : _ = _ |- _ ] => rewrite H
              | [ H : reg |- _ ] => destruct H
            end; intuition); subst.
(*
    Lemma sym_evalLoc_correct : forall loc ss res res' stn_st locD cs,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_locD funcs meta_env vars_env loc = Some locD ->
      evalLoc (snd stn_st) locD = res' ->
      sym_evalLoc loc ss = res -> 
      exprD funcs meta_env vars_env res tvWord = Some res'.
    Proof.
      destruct loc; unfold stateD; destruct ss; destruct SymRegs; destruct p; subst funcs; t_correct.
    Qed.
    
    Hypothesis Valid_facts : Valid PC meta_env vars_env facts.
    
    Lemma sym_evalRval_correct : forall rv ss res stn_st rvD cs,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_rvalueD funcs meta_env vars_env rv = Some rvD ->
      sym_evalRval Prover meval facts rv ss = Some res ->
      exists val,
        evalRvalue (fst stn_st) (snd stn_st) rvD = Some val /\
        exprD funcs meta_env vars_env res tvWord = Some val.
    Proof.
      destruct rv; unfold stateD; t_correct; try congruence;
        try solve [ destruct ss; destruct SymRegs; destruct p; intuition; t_correct; eauto ].

      destruct s; t_correct; destruct ss; destruct SymRegs; destruct p; intuition; t_correct; eauto.
      t_correct;
      match goal with
        | [ H : MEVAL.smemeval_read_word _ _ _ _ _ = _ |- _ ] => 
          eapply (MEVAL.ReadCorrect meval_correct) in H; eauto; t_correct
      end; eauto.
      eapply sym_evalLoc_correct with (cs := cs); eauto. instantiate (1 := (s0, s1)). t_correct.
      reflexivity.
      congruence.
    Qed.
          
    Lemma sym_evalLval_correct : forall lv stn_st lvD cs val ss ss' valD,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_lvalueD funcs meta_env vars_env lv = Some lvD ->
      sym_evalLval Prover meval facts lv val ss = Some ss' ->
      exprD funcs meta_env vars_env val tvWord = Some valD ->
      exists st', 
        evalLvalue (fst stn_st) (snd stn_st) lvD valD = Some st' /\
        stateD funcs preds meta_env vars_env cs (fst stn_st, st') ss'.
    Proof.
      destruct lv.
        Focus.
        destruct ss; destruct SymRegs; destruct p. unfold funcs in *.
          t_correct; eexists; repeat (split; try reflexivity; eauto);
            try solve [ repeat rewrite sepFormula_eq in *; unfold sepFormula_def in *; simpl in *; auto ].

        Focus.
        unfold funcs in *.
        t_correct.
        eapply sym_evalLoc_correct with (stn_st := (s0, s1)) in H0; simpl in *; eauto.
        destruct ss; intuition. destruct SymRegs. destruct p. simpl in *. subst. intuition.
        repeat match type of H1 with
                 | match ?X with | Some _ => _ | None => _ end => destruct X; try contradiction
               end.            
        match goal with
          | [ H : MEVAL.smemeval_write_word _ _ _ _ _ _ = _ |- _ ] => 
            eapply (MEVAL.WriteCorrect meval_correct) with (cs := cs) (stn_m := (s0,s1)) in H; eauto
        end.
        destruct (WriteWord s0 (Mem s1) (evalLoc s1 l) valD); try contradiction.
        eexists; split; [ reflexivity | ]. intuition.

        generalize SEP.sheapD_pures. unfold SEP.ST.satisfies. intro XXX. 
        rewrite sepFormula_eq in H3. unfold sepFormula_def in H3. simpl in *.
        specialize (@XXX _ _ _ _ preds _ _ cs meta_env vars_env s3 H3). 
        apply AllProvable_app' in H5. apply AllProvable_app; intuition auto.
    Qed.

    Lemma sym_evalInstr_correct' : forall instr stn_st instrD cs ss ss',
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_instrD funcs meta_env vars_env instr = Some instrD ->
      sym_evalInstr Prover meval facts instr ss = Some ss' ->
      exists st',
        evalInstr (fst stn_st) (snd stn_st) instrD = Some st' /\
        stateD funcs preds meta_env vars_env cs (fst stn_st, st') ss'.
    Proof.
      Opaque stateD.
      destruct instr; unfold funcs in *; t_correct; simpl.
      eapply sym_evalRval_correct in H1; eauto; simpl in *.
      destruct H1. intuition.
      eapply sym_evalLval_correct in H2; eauto; simpl in *.
      destruct H2. intuition. unfold funcs in *; t_correct; eauto.

      repeat match goal with
               | [ H : _ |- _ ] => progress fold funcs in H
               | [ H : exists x, _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H 
               | [ H : sym_rvalueD _ _ _ _ = _ |- _ ] =>
                 eapply sym_evalRval_correct in H; eauto
             end.
      
      destruct b; eapply sym_evalLval_correct in H3; eauto; unfold funcs in *; t_correct; eauto.
    Qed.

    Lemma sym_assertTest_correct' : forall cs r rD t l lD ss stn_st,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_rvalueD funcs meta_env vars_env r = Some rD ->
      sym_rvalueD funcs meta_env vars_env l = Some lD ->
      match Structured.evalCond rD t lD (fst stn_st) (snd stn_st) with
        | None =>
          forall res, 
            match sym_assertTest Prover meval facts r t l ss res with
              | Some _ => False
              | None => True
            end
        | Some res' =>
          match sym_assertTest Prover meval facts r t l ss res' with
            | Some b => 
              Provable funcs meta_env vars_env b
            | None => True
          end
      end.
    Proof.
      unfold sym_assertTest; unfold Structured.evalCond; intros;
        repeat match goal with
                 | [ |- context [ sym_evalRval ?A ?B ?F ?X ?Y ] ] =>
                   case_eq (sym_evalRval A B F X Y); intros
                 | [ |- match ?X with 
                          | None => True
                          | Some _ => True
                        end ] => destruct X; trivial
               end.
      case_eq (sym_evalRval Prover meval facts l ss); 
        case_eq (sym_evalRval Prover meval facts r ss); intros;
          try solve [ match goal with
                        | [ |- match ?X with
                                 | Some _ => _ | None => _ 
                               end ] => destruct X; intros
                      end;
          repeat match goal with
                   | [ H : _ = _ |- _ ] => rewrite H
                   | [ |- context [ match ?X with 
                                      | true => _ | false => _ 
                                    end ] ] => destruct X
                   | [ |- context [ match ?X with 
                                      | IL.Eq => _ | Ne => _ | IL.Lt => _ | Le => _ 
                                    end ] ] => destruct X
                 end; trivial ].
      repeat match goal with
               | [ H : sym_rvalueD _ _ _ _ = Some _ |- _ ] =>
                 generalize H ; eapply sym_evalRval_correct in H; eauto
               | [ H : exists x, _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : _ = _ |- _ ] => rewrite H
             end. intros.
      unfold Provable; destruct t;
        repeat (trivial; simpl;
          match goal with
            | [ |- context [ match ?X with
                               | true => _
                               | false => _
                             end ] ] => 
            case_eq X; intros
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ H : _ = _ |- _ ] => rewrite H
          end);
        unfold funcs in *; simpl in *;
          repeat match goal with 
                   | [ H : exprD _ _ _ _ _ = _ |- _ ] => rewrite H
                   | [ H : @eq bool (?F _ _) _ |- _ ] => revert H ; clear ; unfold F ; intros
                 end; simpl;
          repeat match goal with
                   | [ H : match ?X with 
                             | left _ => _
                             | right _ => _ 
                           end = _ |- _ ] => destruct X; try congruence
                 end;
      eauto 10 using eq_le, lt_le, le_neq_lt.
    Qed.
*)
  End typed.


  Section typed2.
    Variable ts : list type.
    Let types := repr bedrock_types_r ts.

    Local Notation "'pcT'" := tvWord.
    Local Notation "'stT'" := (tvType 0).
    Local Notation "'tvState'" := (tvType 1).
    Local Notation "'tvTest'" := (tvType 2).
    Local Notation "'tvReg'" := (tvType 3).

    Variable fs : functions types.
    Let funcs := repr (bedrock_funcs_r ts) fs.
    Variable preds : SEP.predicates types pcT stT.

    Variable Prover : ProverT types.
    Variable PC : ProverT_correct Prover funcs.

    Variable meval : MEVAL.MemEvaluator types pcT stT.
    Variable meval_correct : MEVAL.MemEvaluator_correct meval funcs preds tvWord tvWord
      (@IL_mem_satisfies ts) (@IL_ReadWord ts) (@IL_WriteWord ts).

    Local Ltac t_correct := 
      simpl; intros;
        unfold IL_stn_st, IL_mem_satisfies, IL_ReadWord, IL_WriteWord in *;
          repeat (simpl in *; 
            match goal with
              | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
              | [ H : prod _ _ |- _ ] => destruct H
              | [ H : match ?X with 
                        | Some _ => _
                        | None => _ 
                      end |- _ ] =>
              revert H; case_eq X; intros; try contradiction
              | [ H : match ?X with 
                        | Some _ => _
                        | None => _ 
                      end = _ |- _ ] =>
              revert H; case_eq X; intros; try congruence
              | [ H : _ = _ |- _ ] => rewrite H
              | [ H : reg |- _ ] => destruct H
            end; intuition); subst.

    Lemma sym_evalInstrs_correct : forall (facts : Facts Prover) (meta_env var_env : env types),
      Valid PC meta_env var_env facts  ->
      forall is stn_st isD cs ss,
        stateD funcs preds meta_env var_env cs stn_st ss ->
        sym_instrsD funcs meta_env var_env is = Some isD ->
        match evalInstrs (fst stn_st) (snd stn_st) isD with
          | Some st' => 
            match sym_evalInstrs Prover meval facts is ss with
              | inl ss' => stateD funcs preds meta_env var_env cs (fst stn_st, st') ss'
              | inr (ss', is') => 
                match sym_instrsD funcs meta_env var_env is' with
                  | None => False
                  | Some is'D => 
                    exists st'', stateD funcs preds meta_env var_env cs (fst stn_st, st'') ss' /\
                      evalInstrs (fst stn_st) st'' is'D = Some st'
                end
            end
          | None => 
            match sym_evalInstrs Prover meval facts is ss with
              | inl ss' => False
              | inr (ss', is') => 
                match sym_instrsD funcs meta_env var_env is' with
                  | None => False
                  | Some is'D => 
                    exists st'', stateD funcs preds meta_env var_env cs (fst stn_st, st'') ss' /\
                      evalInstrs (fst stn_st) st'' is'D = None
                end
            end
        end.
    Proof.
(*
      Opaque stateD.
      induction is; simpl; intros;
        repeat match goal with
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               end; simpl; destruct stn_st; simpl in *; eauto.

      t_correct. simpl in *.
      case_eq (evalInstr s s0 i); intros.
      case_eq (sym_evalInstr Prover meval facts a ss); intros.      

      Check sym_evalInstr_correct'.

      destruct (@sym_evalInstr_correct' ts fs preds Prover PC meval meval_correct facts meta_env var_env
        H a (s,s0) i cs ss s2 H0 H1 H4). simpl in *. intuition.
      rewrite H6 in H3. inversion H3; clear H3; subst.
      specialize (IHis (s, s1)). simpl in *. eapply IHis; eauto.
      
      simpl. rewrite H1. rewrite H2. simpl. 
      case_eq (evalInstrs s s1 l); intros; exists s0; simpl; rewrite H3; eauto.

      case_eq (sym_evalInstr Prover meval facts a ss); intros. 
      Focus 2. simpl. rewrite H1. rewrite H2. exists s0; simpl; rewrite H3; intuition.

      

      edestruct (@sym_evalInstr_correct' ts fs preds Prover PC meval meval_correct facts meta_env var_env
        H a (s,s0) i cs ss); eauto.
      simpl in *. destruct H5. rewrite H3 in H5. congruence.
      Transparent stateD.
*)
      admit.
    Qed.

    Variable learnHook : MEVAL.LearnHook types (SymState types pcT stT).
    Variable learn_correct : @MEVAL.LearnHook_correct _ _ pcT stT learnHook (@stateD _ funcs preds) funcs preds.

    Theorem evalStream_correct : forall sound_or_safe path stn uvars vars st,
      istreamD funcs uvars vars path stn st sound_or_safe ->
      forall cs ss,
        stateD funcs preds uvars vars cs (stn,st) ss ->
        forall facts, 
          Valid PC uvars vars facts ->
          let res := sym_evalStream Prover meval learnHook facts path ss in
            match res with
              | inl None => 
                match sound_or_safe with
                  | None => True
                  | Some _ => False
                end
              | inl (Some ss') => 
                match sound_or_safe with
                  | None => False
                  | Some st' => 
                    Expr.forallEach (env_ext (length vars) (SymVars ss')) (fun venv =>
                      let var_env := vars ++ venv in
                        Expr.existsEach (env_ext (length uvars) (SymUVars ss')) (fun uenv' =>
                          let meta_env := uvars ++ uenv' in 
                            stateD funcs preds meta_env var_env cs (stn, st') ss'))
                end
              | inr (ss'', is') => 
                exists st'' : state, 
                  Expr.forallEach (env_ext (length vars) (SymVars ss'')) (fun venv =>
                    let var_env := vars ++ venv in
                      Expr.existsEach (env_ext (length uvars) (SymUVars ss'')) (fun uenv' =>
                        let meta_env := uvars ++ uenv' in 
                          istreamD funcs meta_env var_env is' stn st'' None
                          /\ stateD funcs preds meta_env var_env cs (stn, st'') ss''))
            end.
    Proof.
      revert learn_correct; revert PC; revert meval_correct. admit.
(*
    Opaque stateD.
    induction path; simpl; intros;
      repeat match goal with
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end; subst; eauto.
    t_correct. destruct a; t_correct.
        Focus.
          eapply sym_evalInstrs_correct in H; eauto. simpl in *.
          rewrite H4 in *.
          revert H; case_eq (sym_evalInstrs Prover meval facts l ss); intros.
          specialize (IHpath _ _ H5 _ _ H2 _ H1); eauto.
          destruct p. simpl. destruct (sym_instrsD l1); try congruence.
          destruct H2. destruct sound_or_safe; intuition eauto. contradiction.

        Focus.
          eapply sym_evalInstrs_correct in H; eauto; simpl in *.
          rewrite H3 in *.
          destruct (sym_evalInstrs facts l ss); try contradiction.
          destruct p. simpl. destruct (sym_instrsD l1); try contradiction.
          destruct H; intuition; destruct sound_or_safe; eauto.

        Focus.
          destruct s. revert H.
          case_eq (sym_rvalueD s); case_eq (sym_rvalueD s0); intros; try contradiction.
          destruct o.
          generalize (sym_assertTest_correct facts _ _ t _ _ _ H0 H2 H b).
          simpl. destruct H3. rewrite H3.
          case_eq (sym_assertTest facts s t s0 ss b); intros.
          eapply IHpath; eauto.
          
          destruct 
*)
    Admitted.
  End typed2.


(*
  Section iface.
    Variable ts : list type.
    Let types := repr bedrock_types_r ts.

    Local Notation "'pcT'" := (tvType 0).
    Local Notation "'tvWord'" := (tvType 0).
    Local Notation "'stT'" := (tvType 1).
    Local Notation "'tvState'" := (tvType 2).
    Local Notation "'tvTest'" := (tvType 3).
    Local Notation "'tvReg'" := (tvType 4).

    Theorem sym_evalInstr_correct : 
      forall (fs : functions types) (preds : SEP.predicates types (tvType 0) (tvType 1)),
        let funcs := repr (bedrock_funcs_r ts) fs in
        forall (Prover : ProverT types) (PC : ProverT_correct Prover funcs)
          (meval : MEVAL.MemEvaluator types (tvType 0) (tvType 1))
          (meval_correct : MEVAL.MemEvaluator_correct meval funcs preds (tvType 0) (tvType 0)
            (@IL_mem_satisfies ts) (@IL_ReadWord ts) (@IL_WriteWord ts)),
      
        forall (facts : Facts Prover) (meta_env var_env : env types) instr stn_st instrD cs ss ss',
        Valid PC meta_env var_env facts  ->
        stateD funcs preds meta_env var_env cs stn_st ss ->
        sym_instrD funcs meta_env var_env instr = Some instrD ->
        sym_evalInstr Prover meval facts instr ss = Some ss' ->
        exists st',
          evalInstr (fst stn_st) (snd stn_st) instrD = Some st' /\
          stateD funcs preds meta_env var_env cs (fst stn_st, st') ss'.
    Proof.
      intros. eapply sym_evalInstr_correct'; eauto.
    Qed.

    Theorem sym_assertTest_correct : 
      forall (fs : functions types) (preds : SEP.predicates types (tvType 0) (tvType 1)),
        let funcs := repr (bedrock_funcs_r ts) fs in
        forall (Prover : ProverT types) (PC : ProverT_correct Prover funcs)
          (meval : MEVAL.MemEvaluator types (tvType 0) (tvType 1))
          (meval_correct : MEVAL.MemEvaluator_correct meval funcs preds (tvType 0) (tvType 0)
            (@IL_mem_satisfies ts) (@IL_ReadWord ts) (@IL_WriteWord ts)),
          forall (facts : Facts Prover) (meta_env var_env : env types) cs r rD t l lD ss stn_st,
            Valid PC meta_env var_env facts  ->
            stateD funcs preds meta_env var_env cs stn_st ss ->
            sym_rvalueD funcs meta_env var_env r = Some rD ->
            sym_rvalueD funcs meta_env var_env l = Some lD ->
              match Structured.evalCond rD t lD (fst stn_st) (snd stn_st) with
                | None =>
                  forall res, 
                    match sym_assertTest Prover meval facts r t l ss res with
                      | Some _ => False
                      | None => True
                    end
                | Some res' =>
                  match sym_assertTest Prover meval facts r t l ss res' with
                    | Some b => 
                      Provable funcs meta_env var_env b
                    | None => True
                  end
              end.
    Proof.
      intros; eapply sym_assertTest_correct'; eauto.
    Qed.
  End iface.
*)

End SymIL_Correct.

