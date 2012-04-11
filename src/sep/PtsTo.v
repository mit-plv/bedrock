Require Import DepList List.
Require Import Expr SepExpr SymEval.
Require Import Memory SepIL SymIL ILTac.
Require Import Prover.

Set Implicit Arguments.
Set Strict Implicit.

Module BedrockPtsToEvaluator.

  Section hide_notation.
    Local Notation "'pcT'" := (tvType 0).
    Local Notation "'stT'" := (tvType 1).
    Local Notation "'wordT'" := (tvType 0).
    Local Notation "'ptrT'" := (tvType 0).

    Definition ptsto32_types_r : Env.Repr Expr.type :=
      Eval cbv beta iota zeta delta [ Env.listToRepr ] 
      in 
      let lst := 
        {| Impl := W 
         ; Eq := seq_dec |} ::
        {| Impl := IL.settings * IL.state
         ; Eq := fun _ _ => None
         |} :: nil
      in
      Env.listToRepr lst EmptySet_type.

    Section parametric.
      Variable types : list type.
      Variable Prover : ProverT types.

      Definition psummary := Facts Prover.

      Definition expr_equal (sum : psummary) (tv : tvar) (a b : expr types) : bool :=
        match seq_dec a b with
          | Some _ => true
          | None => Prove Prover sum (Equal tv a b)
      end.
    
      Definition sym_read_word_ptsto32 (summ : psummary) (args : list (expr types)) (p : expr types) 
        : option (expr types) :=
        match args with
          | p' :: v' :: nil => 
            if expr_equal summ ptrT p p' then Some v' else None
          | _ => None
        end.
      Definition sym_write_word_ptsto32 (summ : psummary) (args : list (expr types)) (p v : expr types)
        : option (list (expr types)) :=
        match args with
          | p' :: v' :: nil =>
            if expr_equal summ ptrT p p' then Some (p :: v :: nil) else None
          | _ => None
        end.
  End parametric.

  Definition MemEval_ptsto32 types : @MEVAL.Plugin.MemEvalPred types.
  eapply MEVAL.Plugin.Build_MemEvalPred.
  eapply sym_read_word_ptsto32.
  eapply sym_write_word_ptsto32.
  Defined.

  Section correctness.
    Variable types' : list type.
    Definition types := Env.repr ptsto32_types_r types'.

    Local Notation "'pcT'" := (tvType 0).
    Local Notation "'stT'" := (tvType 1).
    Local Notation "'wordT'" := (tvType 0).
    Local Notation "'ptrT'" := (tvType 0).

    Definition ptsto32_ssig : SEP.ssignature types pcT stT.
    refine (
      {| SepExpr.SDomain := ptrT :: wordT :: nil
       ; SepExpr.SDenotation := _
       |}).
    refine (ptsto32 _).
    Defined.

    Variable funcs : functions types.
    Variable Prover : ProverT types.
    Variable Prover_correct : ProverT_correct Prover funcs.

    Theorem expr_equal_correct : 
      forall (sum : Facts Prover) (tv : tvar) (a b : expr types),
        expr_equal Prover sum tv a b = true ->
        forall uvars vars,
          Valid Prover_correct uvars vars sum ->
          match exprD funcs uvars vars a tv , exprD funcs uvars vars b tv with 
            | Some l , Some r => l = r
            | _ , _ => True
          end.
    Proof.
      unfold expr_equal. intros. destruct (seq_dec a b); subst.
      destruct (exprD funcs uvars vars b tv); auto.
      generalize (Prove_correct Prover_correct). intro XX; apply XX in H0; clear XX.
      case_eq (exprD funcs uvars vars a tv); auto.
      case_eq (exprD funcs uvars vars b tv); auto.
      intros; eapply H0 in H. unfold Provable in H. simpl in H. 
      intros. rewrite H1 in *. rewrite H2 in *. auto. 

      unfold ValidProp. simpl. rewrite H1. rewrite H2. eauto.
    Qed.

    Ltac expose :=
      repeat (
        match goal with 
          | [ H : match applyD _ _ ?A _ _ with
                    | Some _ => _ 
                    | None => False 
                  end |- _ ] =>
          destruct A; simpl in H; try (exfalso; assumption)
          | [ H : context [ match exprD ?A ?B ?C ?D ?E with
                              | None => _
                              | Some _ => _
                            end ] |- _ ] =>
          revert H; case_eq (exprD A B C D E); simpl; intros; 
            try (exfalso; assumption)
          | [ H : context [ match expr_equal ?A ?B ?C ?D with
                              | true => _
                              | false => _
                            end ] |- _ ] =>
          revert H; case_eq (expr_equal A B C D); intros; 
            try (exfalso; congruence)
          | [ H : expr_equal ?A ?B ?C ?D = true 
            , H' : AllProvable _ _ _ ?A |- _ ] =>
          generalize (@expr_equal_correct _ _ _ _ H _ _ H'); clear H; intros
          | [ H : Some _ = Some _ |- _ ] =>
            inversion H; clear H; subst
          | [ H : exprD _ _ _ _ _ = Some _ |- _ ] =>
            rewrite H in *
        end; simpl in * ).

    Lemma sym_read_ptsto32_correct : forall args uvars vars cs summ pe p ve m stn,
      sym_read_word_ptsto32 Prover summ args pe = Some ve ->
      Valid Prover_correct uvars vars summ ->
      exprD funcs uvars vars pe ptrT = Some p ->
      match 
        applyD (exprD funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
        with
        | None => False
        | Some p => ST.satisfies cs p stn m
      end ->
      match exprD funcs uvars vars ve wordT with
        | Some v =>
          ST.HT.smem_get_word (IL.implode stn) p m = Some v
        | _ => False
      end.
    Proof.
      simpl; intros.
      unfold sym_read_word_ptsto32 in H.
      repeat (destruct args; try congruence).
      revert H.
      case_eq (expr_equal Prover summ ptrT pe e); try congruence.
      intros.
      inversion H3; clear H3; subst.
      eapply expr_equal_correct in H; eauto.
      simpl applyD in H2.
      expose; try congruence.
      unfold ST.satisfies in H6. PropXTac.propxFo. 
    Qed.

    Lemma sym_write_word_ptsto32_correct : forall args uvars vars cs summ pe p ve v m stn args',
      sym_write_word_ptsto32 Prover summ args pe ve = Some args' ->
      Valid Prover_correct uvars vars summ ->
      exprD funcs uvars vars pe ptrT = Some p ->
      exprD funcs uvars vars ve wordT = Some v ->
      match
        applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
        with
        | None => False
        | Some p => ST.satisfies cs p stn m
      end ->
      match 
        applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args' _ (SDenotation ptsto32_ssig)
        with
        | None => False
        | Some pr => 
          match ST.HT.smem_set_word (IL.explode stn) p v m with
            | None => False
            | Some sm' => ST.satisfies cs pr stn sm'
          end
      end.
    Proof.
      simpl; intros; expose.
      revert H; case_eq (expr_equal Prover summ ptrT pe e); intros; try congruence.
      inversion H6; clear H6; subst. simpl.
      rewrite H1. rewrite H2.
      
      case_eq (smem_set_word (IL.explode stn) p v m); intros; unfold ptsto32 in *. 
      PropXTac.propxFo.
      eapply smem_set_get_word_eq; eauto.
      eapply IL.implode_explode.
      eapply expr_equal_correct in H; eauto.
      rewrite H1 in H. rewrite H3 in H. subst.
      unfold ST.satisfies in H5. PropXTac.propxFo.
      eapply smem_set_get_valid_word; eauto.
    Qed.  

  End correctness.

  Definition MemEval_ptsto32_correct types' funcs
    : @MEVAL.Plugin.MemEvalPred_correct _ (MemEval_ptsto32 (Env.repr ptsto32_types_r types')) (tvType 0) (tvType 1) (IL.settings * IL.state) (tvType 0) (tvType 0)
    (@IL_mem_satisfies types') (@IL_ReadWord types') (@IL_WriteWord types') (ptsto32_ssig types') funcs.
  Proof.
    eapply MEVAL.Plugin.Build_MemEvalPred_correct;
      simpl; unfold MemEval_ptsto32, IL_ReadWord, IL_WriteWord, IL_mem_satisfies, IL.ReadWord, IL.WriteWord.
    destruct stn_st; simpl in *.
    (** TODO: the interface is wrong, it needs to be over the symbolic memory **)
  Admitted.
  End hide_notation.

  Definition ptsto32_pack : MEVAL.MemEvaluatorPackage ptsto32_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) IL_mem_satisfies IL_ReadWord IL_WriteWord.
  refine ({| MEVAL.MemEvalTypes := Env.nil_Repr EmptySet_type
           ; MEVAL.MemEvalFuncs := fun ts => Env.nil_Repr (Default_signature (Env.repr ptsto32_types_r ts))
           ; MEVAL.MemEvalPreds := fun ts => Env.listToRepr (ptsto32_ssig ts :: nil)
             (SymIL.SEP.Default_ssignature (Env.repr ptsto32_types_r ts)
               (tvType 0) (tvType 1))
           ; MEVAL.MemEval := fun ts => MEVAL.Plugin.MemEvaluator_plugin (tvType 0) (tvType 1) ((0,MemEval_ptsto32 (types ts)) :: nil)
           ; MEVAL.MemEval_correct := fun ts fs ps =>
             MEVAL.Plugin.PluginMemEvaluator_correct _ _ _ _ _ _ _ _ _
    |}).
  abstract (split; simpl; eapply MemEval_ptsto32_correct with (types' := ts) || exact I).
  Defined.
(*
About Build_TypedPackage.

Ltac build_mem_pack mem ret :=
  match type of mem with
    | @MEVAL.MemEvaluatorPackage ?tr ?pc ?st IL_mem_satisfies IL_ReadWord IL_WriteWord =>
      (let res := constr:(
        let TR := Env.repr_combine (MEVAL.MemEvalTypes mem) tr in
        @Build_TypedPackage ILEnv.bedrock_types_r (tvType 0) (tvType 1) 
          SymIL.IL_mem_satisfies SymIL.IL_ReadWord SymIL.IL_WriteWord
          TR
          (fun ts => MEVAL.MemEvalFuncs mem (Env.repr TR (Env.repr ILEnv.bedrock_types_r ts)))
          (fun ts => MEVAL.MemEvalPreds mem (Env.repr TR (Env.repr ILEnv.bedrock_types_r ts)))
          (fun ts =>
            {| SymIL.Prover  := None
             ; SymIL.Hints   := None
             ; SymIL.MemEval := Some (MEVAL.MemEval mem (Env.repr ILEnv.bedrock_types_r ts))
            |})
          (fun ts fs ps =>
           let types := Env.repr ILEnv.bedrock_types_r (Env.repr tr ts) in
           @Build_AllAlgos_correct types pc st
             ({| SymIL.Prover := None
               ; SymIL.Hints := None
               ; SymIL.MemEval := Some (MEVAL.MemEval mem (Env.repr ILEnv.bedrock_types_r ts))
               |})
             _ _ (@IL_mem_satisfies _) (@IL_ReadWord _) (@IL_WriteWord _)
             I I
             (MEVAL.MemEval_correct mem (Env.repr ILEnv.bedrock_types_r ts) fs ps))) in
      let res := eval simpl in res in
      ret res) || fail 10000 "couldn't construct mem_package"
    | ?T => 
      fail 10000 "got bad type" T "expected value of type Packages.MemEvaluatorPackage"
  end.
*)
Goal SymIL.TypedPackage ILEnv.bedrock_types_r (Expr.tvType 0) (Expr.tvType 1) SymIL.IL_mem_satisfies SymIL.IL_ReadWord SymIL.IL_WriteWord.
  SymIL.Package.build_mem_pack ptsto32_pack ltac:(fun x => refine x).
Abort.
End BedrockPtsToEvaluator.

