Require Import DepList List.
Require Import Expr SepExpr SymEval.
Require Import Memory SepIL SepTac.

Module BedrockPtsToEvaluator (P : EvaluatorPluginType BedrockHeap SepIL.ST).
  Module Import SEP := P.SEP.

  Definition pcIndex : nat := 0.
  Definition stateIndex : nat := 1.
  
  Definition addr_type :=
    {| Impl := W
     ; Eq := seq_dec 
     |}.

  Definition word_type :=
    {| Impl := W
     ; Eq := seq_dec 
     |}.

  Definition wtypes := bedrock_types.

  Definition wordIndex := 0.
  Definition ptrIndex := 0.

  Definition ptsto32_ssig : ssignature wtypes (tvType pcIndex) (tvType stateIndex).
  refine (
  {| SepExpr.SDomain := tvType ptrIndex :: tvType wordIndex :: nil
   ; SepExpr.SDenotation := _
   |}).
  refine (ptsto32 _).
  Defined.

  Section with_functions.
  Variable funcs : functions wtypes.

  (** TODO: maybe this should be like unification? 
   ** - in that case the substitution is an effect and needs to be
   **   threaded through the computation (monadically?)
   **)
  Variable expr_equal : forall (hyps : list (expr wtypes)) (tv : tvar) (a b : expr wtypes), bool.
  Variable expr_equal_correct : 
    forall (hyps : list (expr wtypes)) (tv : tvar) (a b : expr wtypes),
      expr_equal hyps tv a b = true ->
      forall uvars vars, 
        AllProvable funcs uvars vars hyps ->
        match exprD funcs uvars vars a tv , exprD funcs uvars vars b tv with 
          | Some l , Some r => l = r
          | _ , _ => False
        end.

  Definition sym_read_word_ptsto32 (hyps args : list (expr wtypes)) (p : expr wtypes) 
    : option (expr wtypes) :=
    match args with
      | p' :: v' :: nil => 
        if expr_equal hyps (tvType ptrIndex) p p' then Some v' else None
      | _ => None
    end.
  Definition sym_write_word_ptsto32 (hyps args : list (expr wtypes)) (p v : expr wtypes)
    : option (list (expr wtypes)) :=
    match args with
      | p' :: v' :: nil =>
        if expr_equal hyps (tvType ptrIndex) p p' then Some (p :: v :: nil) else None
      | _ => None
    end.

  Ltac expose :=
    repeat (unfold wordIndex, ptrIndex in *; 
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
              generalize dependent H; case_eq (exprD A B C D E); simpl; intros; 
                try (exfalso; assumption)
              | [ H : context [ match expr_equal ?A ?B ?C ?D with
                                  | true => _
                                  | false => _
                                end ] |- _ ] =>
                generalize dependent H; case_eq (expr_equal A B C D); intros; 
                  try (exfalso; congruence)
              | [ H : expr_equal ?A ?B ?C ?D = true 
                , H' : AllProvable _ _ _ ?A |- _ ] =>
                generalize (@expr_equal_correct _ _ _ _ H _ _ H'); clear H; intros
              | [ H : Some _ = Some _ |- _ ] =>
                inversion H; clear H; subst
              | [ H : exprD _ _ _ _ _ = Some _ |- _ ] =>
                rewrite H in *
            end; simpl in * ).

  Lemma sym_read_ptsto32_correct : forall args uvars vars cs hyps pe ve m stn,
    sym_read_word_ptsto32 hyps args pe = Some ve ->
    AllProvable funcs uvars vars hyps ->
    match 
      applyD (exprD funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars pe (tvType ptrIndex) , exprD funcs uvars vars ve (tvType wordIndex) with
      | Some p , Some v =>
        ST.HT.smem_get_word (IL.implode stn) p m = Some v
      | _ , _ => False
    end.
  Proof.
    simpl; intros; expose.
    unfold ST.satisfies in H3. PropXTac.propxFo.
  Qed.

  Lemma sym_write_word_ptsto32_correct : forall args uvars vars cs hyps pe ve v m stn args',
    sym_write_word_ptsto32 hyps args pe ve = Some args' ->
    AllProvable funcs uvars vars hyps ->
    exprD funcs uvars vars ve (tvType wordIndex) = Some v ->
    match
      applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars pe (tvType ptrIndex)with
      | Some p =>
        match 
          applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args' _ (SDenotation ptsto32_ssig)
          with
          | None => False
          | Some pr => 
            match ST.HT.smem_set_word (IL.explode stn) p v m with
              | None => False
              | Some sm' => ST.satisfies cs pr stn sm'
            end
        end
      | _ => False
    end.
  Proof.
    simpl; intros; expose.

    unfold ST.satisfies in *. PropXTac.propxFo. 
    case_eq (smem_set_word (IL.explode stn) t v m).
    intros. unfold ptsto32. PropXTac.propxFo.
    eapply smem_set_get_word_eq; eauto.
    eapply IL.implode_explode.
    eapply smem_set_get_valid_word; eauto.
  Qed.  

  Definition SymEval_ptsto32 : @P.SymEval wtypes (tvType stateIndex) (tvType pcIndex) 
    (tvType ptrIndex) (tvType wordIndex)
    (fun stn => ST.HT.smem_get_word (IL.implode stn))
    (fun stn => ST.HT.smem_set_word (IL.explode stn))
    funcs ptsto32_ssig.
  eapply P.Build_SymEval.
  eapply sym_read_ptsto32_correct.
  eapply sym_write_word_ptsto32_correct.
  Defined.  
  End with_functions.

End BedrockPtsToEvaluator.
