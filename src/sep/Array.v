Require Import DepList List.
Require Import Expr SepExpr SymEval.
Require Import Word Memory IL SepIL SepTac.
Require Import EqdepClass.

Module BedrockArrayEvaluator (P : EvaluatorPluginType BedrockHeap SepIL.ST).
  Module Import SEP := P.SEP.

  Definition pcIndex : nat := 0.
  Definition stateIndex : nat := 1.
  
  Definition content_type :=
    {| Expr.Impl := list W
     ; Expr.Eq := seq_dec 
     |}.

  Definition types := bedrock_types ++ content_type :: nil.

  Fixpoint wbuffer (st : W) (ls : list W) : hprop (tvarD types (tvType pcIndex)) (tvarD types (tvType stateIndex)) nil :=
    match ls with
      | nil => emp _ _ 
      | l :: ls =>
        st ==> l * wbuffer (st ^+ $ 4)  ls
    end%Sep.

  Definition wbuffer_ssig : ssignature types (tvType pcIndex) (tvType stateIndex).
  refine (
  {| SepExpr.SDomain := tvType 0 :: tvType 2 :: nil
   ; SepExpr.SDenotation := _
   |}).
  refine (wbuffer).
  Defined.

  Definition wordIndex := 0.
  Definition ptrIndex := 0.

  Variable funcs' : functions types.

  Variable plusIdx : nat.
  Variable consIdx : nat.
  Hypothesis plusIdx_consIdx : plusIdx <> consIdx.

  Definition plus_sig : signature types.
    refine (
  {| Expr.Domain := tvType wordIndex :: tvType wordIndex :: nil
   ; Expr.Range := tvType wordIndex
   ; Expr.Denotation := _
   |}); simpl.
    eapply wplus.
  Defined.

  Definition cons_sig : signature types.
    refine (
  {| Expr.Domain := tvType wordIndex :: tvType 2 :: nil
   ; Expr.Range := tvType 2
   ; Expr.Denotation := _
   |}); simpl.
    eapply cons.
  Defined.

  Definition funcs : functions types :=
    Env.updateAt plus_sig (Env.updateAt cons_sig funcs' consIdx) plusIdx.

  Fixpoint get_nth (e : expr types) (n : nat) : option (expr types) :=
    match e with 
      | Expr.Func i (hd :: tl :: nil) =>
        if equiv_dec i consIdx then 
          (* this is a cons cell *)
          match n with
            | 0 => Some hd
            | S n => get_nth tl n
          end
        else None
      | _ => None
    end.

  Lemma get_nth_correct : forall uvars vars e eD n x,
    exprD funcs uvars vars e (tvType 2) = Some eD ->
    get_nth e n = Some x ->
    match exprD funcs uvars vars x (tvType wordIndex) with
      | Some y => nth_error eD n = Some y
      | None => False
    end.
  Proof.
    simpl. induction e; simpl; try congruence.
    intros. 
    repeat match goal with
             | [ H : context [ match ?X with
                                 | nil => _ 
                                 | _ :: _ => _
                               end ] |- _ ] =>
               (destruct X; [ try congruence | try congruence ]); [ ]
             | [ H : context [ equiv_dec ?X ?Y ] |- _ ] =>
               destruct (equiv_dec X Y); try congruence
           end.
    unfold funcs in H0.
    erewrite Env.nth_error_updateAt_not in H0.
    2: rewrite e1; generalize plusIdx_consIdx; eauto.
    2: rewrite e1; eapply Env.nth_error_updateAt.
    simpl in H0.
    fold funcs in *.
    destruct n;
    repeat match goal with
             | [ H : context [ match ?X with
                                 | None => _ 
                                 | Some _ => _
                               end ] |- _ ] =>
               revert H; case_eq X; intros; try congruence
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
           end.
    rewrite H0; auto.
    simpl.
    inversion H; clear H. inversion H6; clear H6. subst. clear H9.
    eapply H8; eauto.
  Qed.

  (** TODO: maybe this should be like unification? 
   ** - in that case the substitution is an effect and needs to be
   **   threaded through the computation (monadically?)
   **)
  Variable expr_equal : forall (hyps : list (expr types)) (tv : tvar) (a b : expr types), bool.
  Variable expr_equal_correct : 
    forall (hyps : list (expr types)) (tv : tvar) (a b : expr types),
      expr_equal hyps tv a b = true ->
      forall uvars vars, 
        AllProvable funcs uvars vars hyps ->
        match exprD funcs uvars vars a tv , exprD funcs uvars vars b tv with 
          | Some l , Some r => l = r
          | _ , _ => False
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


  Definition divBy4 (hyps : list (expr types)) (e : expr types) : option nat :=
    match e with
      | Expr.Const t w => 
        match equiv_dec (tvType 0) t with
          | left pf =>
            match pf in _ = t return tvarD types t -> option nat with
              | refl_equal => fun x => None
            end w
          | right _ => None
        end            
      | _ => None
    end.

  Definition extractIndex (hyps : list (expr types)) (base e : expr types) : option nat := 
    if expr_equal hyps (tvType ptrIndex) e base then 
      Some 0
    else 
      match e with 
        | Expr.Func i (l :: r :: nil) =>
          match equiv_dec i plusIdx , expr_equal hyps (tvType ptrIndex) l base with
            | left _ , true => divBy4 hyps r
            | _ , _ => None
          end
        | _ => None
      end.

  Lemma divBy4_correct : forall uvars vars hyps e eD i,
    divBy4 hyps e = Some i ->
    AllProvable funcs uvars vars hyps ->
    exprD funcs uvars vars e (tvType ptrIndex) = Some eD ->
    eD = $ (4 * i).
  Proof.
    intros. destruct e; simpl in H; try congruence.
    destruct (equiv_dec (tvType 0) t); try congruence.
    unfold equiv in *.
    generalize dependent t0. generalize e.
    rewrite <- e. 
    intro. rewrite (UIP_refl e0). congruence.
  Qed.

  Lemma extractIndex_correct : forall uvars vars hyps b bD e eD i,
    extractIndex hyps b e = Some i ->
    AllProvable funcs uvars vars hyps ->
    exprD funcs uvars vars b (tvType ptrIndex) = Some bD ->
    exprD funcs uvars vars e (tvType ptrIndex) = Some eD ->
    eD = bD ^+ $ (4 * i).
  Proof.
    unfold extractIndex. intros. 
    revert H. case_eq (expr_equal hyps (tvType ptrIndex) e b); intros.
    inversion H3; clear H3; subst.
    eapply expr_equal_correct in H; eauto.
    rewrite H1 in *. rewrite H2 in *. subst. simpl in *. admit.
    
    destruct e; try congruence.
    do 3 match goal with
      | [ H : context [ match ?A with
                          | nil => _ 
                          | _ :: _ => _
                        end ] |- _ ] =>
      (destruct A; simpl in H; try congruence); [ ]
    end.
    clear H.
    destruct (equiv_dec f plusIdx); try congruence.
    rewrite e1 in *. clear e1.
    revert H3. case_eq (expr_equal hyps (tvType ptrIndex) e b); intros; try congruence.

    simpl in H2.
    unfold funcs in H2.
    rewrite Env.nth_error_updateAt in H2. simpl in H2.
    fold funcs in H2.
    eapply expr_equal_correct in H; eauto.
    rewrite H1 in *.
    unfold ptrIndex, wordIndex in *.
    destruct (exprD funcs uvars vars0 e (tvType 0)); subst; try congruence.
    revert H2.
    case_eq (exprD funcs uvars vars0 e0 (tvType 0)); intros; try congruence.
    inversion H2; clear H2; subst.
    eapply divBy4_correct in H3; eauto. subst; eauto.
  Qed.

(*
  Definition sym_read_word_wbuffer (hyps args : list (expr types)) (p : expr types) 
    : option (expr types) :=
    match args with
      | p' :: v' :: nil => 
        if expr_equal hyps (tvType ptrIndex) p p' 
          then Some v'
          else None
      | _ => None
    end.
(*
  Definition sym_write_word_wbuffer (hyps args : list (expr types)) (p v : expr types)
    : option (list (expr types)) :=
    match args with
      | p' :: v' :: nil =>
        if expr_equal hyps (tvType ptrIndex) p p' then Some (p :: v :: nil) else None
      | _ => None
    end.
*)

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

  Lemma sym_read_wbuffer_correct : forall args uvars vars cs hyps pe ve m stn,
    sym_read_word_wbuffer hyps args pe = Some ve ->
    AllProvable funcs uvars vars hyps ->
    match 
      applyD (exprD funcs uvars vars) (SDomain wbuffer_ssig) args _ (SDenotation wbuffer_ssig)
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
    rewrite 
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

  Print P.SymEval.
  
  

  Definition SymEval_ptsto32 : @P.SymEval types (tvType stateIndex) (tvType pcIndex) 
    (tvType ptrIndex) (tvType wordIndex)
    (fun stn => ST.HT.smem_get_word (IL.implode stn))
    (fun stn => ST.HT.smem_set_word (IL.explode stn))
    funcs ptsto32_ssig.
  eapply P.Build_SymEval.
  eapply sym_read_ptsto32_correct.
  eapply sym_write_word_ptsto32_correct.
  Defined.  
*)
End BedrockArrayEvaluator.
