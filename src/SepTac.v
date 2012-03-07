Require Import IL SepIL.
Require Import Word Memory.
Import List.
Require Import DepList EqdepClass.

Require Expr SepExpr.
Module SEP := SepExpr.SepExpr BedrockHeap ST.

Definition bedrock_types : list Expr.type :=
  {| Expr.Impl := W 
   ; Expr.Eq := fun x y => 
     match weq x y with
       | left pf => Some pf 
       | _ => None 
     end |}
  :: {| Expr.Impl := (settings * state)%type
      ; Expr.Eq := fun _ _ => None
      |}
  :: nil.
(*
  :: SEP.defaultType label :: nil.
*)

Definition bedrock_ext (ls : list Expr.type) : list Expr.type :=
  match ls with
    | _ :: _ :: r => r
    | _ => nil
  end.

Lemma ApplyCancelSep : forall types funcs sfuncs (l r : SEP.sexpr (bedrock_types ++ types) (Expr.tvType O) (Expr.tvType 1)),
  (forall cs,
    match SEP.CancelSep nil l r with
      | {| SEP.vars := vars; 
           SEP.lhs := lhs; SEP.rhs_ex := rhs_ex; 
           SEP.rhs := rhs; SEP.SUBST := SUBST |} =>
           SEP.forallEach vars
             (fun VS : Expr.env (bedrock_types ++ types) =>
              SEP.exists_subst funcs VS
                (ExprUnify.env_of_Subst SUBST rhs_ex 0)
                (fun rhs_ex0 : Expr.env (bedrock_types ++ types) =>
                 SEP.himp funcs sfuncs nil rhs_ex0 VS cs lhs rhs))
    end) ->
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil l)
  ===>
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil r).
Proof.
  unfold Himp. intros. specialize (H specs). 
  apply SEP.ApplyCancelSep in H. unfold SEP.himp in *. assumption.
  simpl; tauto.
Qed.


Lemma Himp_to_SEP_himp : forall types funcs sfuncs 
  (l r : @SEP.sexpr (bedrock_types ++ types) (Expr.tvType 0) (Expr.tvType 1)),
  (forall cs, SEP.himp funcs sfuncs nil nil nil cs l r) ->
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil l)
  ===>
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil r).
Proof.
  unfold Himp, SEP.himp. intuition.
Qed.

Ltac reflect_goal isConst Ts :=
  match goal with 
    | [ |- Himp ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
      let types := eval unfold bedrock_types in bedrock_types in
      let goals := constr:(L :: R :: nil) in
      let goals := eval unfold starB exB hvarB in goals in
      let v := SEP.reflect_sexprs pcT stateT ltac:(isConst) types tt tt goals in
      match v with
        | (?types, ?pcT, ?stT, ?funcs, ?sfuncs, ?L :: ?R :: nil) => 
          apply (@Himp_to_SEP_himp _ funcs sfuncs L R)
      end
  end.

(** Symbolic Evaluation **)
Require SymEval.

Module PLUGIN := SymEval.EvaluatorPlugin BedrockHeap ST.

Module BedrockEvaluator.
  Require Import SepExpr SymEval.
  Require Import Expr.

  Module SEP := PLUGIN.SEP.

  Section typed.
    Variable types : list type.
   
  (** These the reflected version of the IL, it essentially 
   ** replaces all uses of W with expr types so that the value
   ** can be inspected.
   **)
  Inductive sym_loc :=
  | SymReg : reg -> sym_loc
  | SymImm : expr types -> sym_loc
  | SymIndir : reg -> expr types -> sym_loc.

  (* Valid targets of assignments *)
  Inductive sym_lvalue :=
  | SymLvReg : reg -> sym_lvalue
  | SymLvMem : sym_loc -> sym_lvalue.
  
  (* Operands *)
  Inductive sym_rvalue :=
  | SymRvLval : sym_lvalue -> sym_rvalue
  | SymRvImm : expr types -> sym_rvalue
  | SymRvLabel : label -> sym_rvalue.

  (* Non-control-flow instructions *)
  Inductive sym_instr :=
  | SymAssign : sym_lvalue -> sym_rvalue -> sym_instr
  | SymBinop : sym_lvalue -> sym_rvalue -> binop -> sym_rvalue -> sym_instr.

  Inductive sym_jmp :=
    SymUncond : sym_rvalue -> sym_jmp
  | SymCond : sym_rvalue -> test -> sym_rvalue -> label -> label -> sym_jmp.

  End typed.

  Implicit Arguments SymReg [ types ].
  Implicit Arguments SymImm [ types ].
  Implicit Arguments SymIndir [ types ].
  Implicit Arguments SymLvReg [ types ].
  Implicit Arguments SymLvMem [ types ].
  Implicit Arguments SymRvLval [ types ].
  Implicit Arguments SymRvImm [ types ].
  Implicit Arguments SymRvLabel [ types ].
  Implicit Arguments SymAssign [ types ].
  Implicit Arguments SymBinop [ types ].
  Implicit Arguments SymUncond [ types ].
  Implicit Arguments SymCond [ types ].

  Section typed_ext.
    Variable types' : list type.
    Definition types := bedrock_types ++ types'.
    Definition pcT := tvType 0.
    Definition tvWord := tvType 0.
    Definition stT := tvType 1.
    Definition tvLabel := tvType 2.
  
  (** Symbolic registers **)
  Definition SymRegType : Type :=
    (expr types * expr types * expr types)%type.

  Definition sym_getReg (r : reg) (sr : SymRegType) : expr types :=
    match r with
      | Sp => fst (fst sr)
      | Rp => snd (fst sr)
      | Rv => snd sr
    end.

  Definition sym_setReg (r : reg) (v : expr types) (sr : SymRegType) : SymRegType :=
    match r with
      | Sp => (v, snd (fst sr), snd sr)
      | Rp => (fst (fst sr), v, snd sr)
      | Rv => (fst sr, v)
    end.

  Definition bedrock_funcs : list (signature types).
  refine ({| Domain := tvWord :: tvWord :: nil
           ; Range := tvWord
           ; Denotation := _ |} ::
          {| Domain := tvWord :: tvWord :: nil
           ; Range := tvWord
           ; Denotation := _ |} ::
          {| Domain := tvWord :: tvWord :: nil
           ; Range := tvWord
           ; Denotation := _ |} ::
(*          {| Domain := tvLabel :: nil 
           ; Range := tvWord 
           ; Denotation := _ |} :: *) nil).
  refine (@wplus 32).
  refine (@wminus 32).
  refine (@wmult 32).
  Defined.  

  Variable funcs' : functions types.
  Definition funcs := bedrock_funcs ++ funcs'.

  Definition fPlus (l r : expr types) : expr types :=
    Expr.Func 0 (l :: r :: nil).
  Definition fMinus (l r : expr types) : expr types :=
    Expr.Func 1 (l :: r :: nil).
  Definition fMult (l r : expr types) : expr types :=
    Expr.Func 2 (l :: r :: nil).

  Theorem fPlus_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fPlus l r) tvWord = Some (wplus lv rv)
      | _ , _ => True
    end.
  Proof.
    intros. simpl.
    repeat match goal with
             | [ |- match ?X with
                      | Some _ => _
                      | None => _
                    end ] => destruct X
           end; auto.
  Qed.
  Theorem fMinus_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fMinus l r) tvWord = Some (wminus lv rv)
      | _ , _ => True
    end.
  Proof.
    intros. simpl.
    repeat match goal with
             | [ |- match ?X with
                      | Some _ => _
                      | None => _
                    end ] => destruct X
           end; auto.
  Qed.
  Theorem fMult_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fMult l r) tvWord = Some (wmult lv rv)
      | _ , _ => True
    end.
  Proof.
    intros. simpl.
    repeat match goal with
             | [ |- match ?X with
                      | Some _ => _
                      | None => _
                    end ] => destruct X
           end; auto.
  Qed.
  Variable sfuncs : list (SEP.ssignature types pcT stT).

  Variable known : list nat.
  Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
  Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).

  Definition evaluators :=
    hlist (fun n : nat => match nth_error sfuncs n with
                            | None => Empty_set 
                            | Some ss => @PLUGIN.SymEval types stT pcT pcT pcT smem_read smem_write funcs ss
                          end) known.
    
  Variable word_evals : evaluators.

  Definition symeval_read_word (hyps : list (expr types)) (p : expr types) 
    (s : SEP.SHeap types pcT stT)
    : option (expr types) :=
    let hyps := hyps ++ SepExpr.pures s in
    let reader ss seb args :=
      @PLUGIN.sym_read _ _ _ _ _ _ _ _ _ seb hyps args p
    in
    SymEval.fold_known _ _ reader (SepExpr.impures s) word_evals.

  Definition symeval_write_word (hyps : list (expr types)) (p v : expr types) 
    (s : SEP.SHeap types pcT stT)
    : option (SEP.SHeap types pcT stT) :=
    let hyps := hyps ++ SepExpr.pures s in
    let writer _ seb args := 
      @PLUGIN.sym_write _ _ _ _ _ _ _ _ _ seb hyps args p v
    in
    match SymEval.fold_known_update _ _ writer (SepExpr.impures s) word_evals with
      | None => None
      | Some i' => Some {| SepExpr.impures := i' ; SepExpr.pures := SepExpr.pures s ; SepExpr.other := SepExpr.other s |}
    end.

(*
  Lemma symeval_write_word_correct' : forall hyps pe ve s s',
    symeval_write_word hyps pe ve s = Some s' ->
    forall cs stn uvars vars m v,
      AllProvable funcs uvars vars hyps ->
      exprD funcs uvars vars ve pcT = Some v ->
      (exists sm, 
           SepIL.ST.satisfies cs (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s)) stn sm
        /\ SepIL.ST.HT.satisfies sm m) ->
      match exprD funcs uvars vars pe pcT with
        | Some p =>
          exists m', 
                mem_set_word _ _  footprint_w SepIL.BedrockHeap.mem_set (IL.explode stn) p v m = Some m'
            /\ exists sm,
               SepIL.ST.satisfies cs (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s')) stn sm
            /\ SepIL.ST.HT.satisfies sm m'
        | _ => False
      end.
  Proof.
    unfold symeval_write_word. intros.
    generalize dependent H.
    match goal with
      | [ |- context [ fold_known_update ?A ?B ?C ?D ?E ] ] =>
        case_eq (fold_known_update A B C D E); intros; try congruence
    end.
    eapply fold_known_update_correct in H.
    do 5 destruct H. destruct H2.
    intuition. inversion H3; clear H3; subst. 
        
    eapply fold_args_update_correct in H6.
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
           end. intuition; subst.
    generalize (SEP.sheapD_pures _ _ _ _ _ H4).
    rewrite SEP.sheapD_pull_impure in H4 by eauto.
    rewrite SEP.starred_In in H4.
    rewrite <- SEP.heq_star_assoc in H4. rewrite SEP.heq_star_comm in H4.
        
    simpl in *. rewrite H2 in *.
    intros.

    eapply SepIL.ST.satisfies_star in H4. do 2 destruct H4. intuition.

    eapply PLUGIN.sym_write_correct with (stn := stn) (cs := cs) (m := x2)
      in H3; eauto.

    2: apply AllProvable_app; eauto.
    2: simpl in *;
    match goal with
      | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
        destruct (applyD A B C D E); try solve [ intros; intuition | eapply SepIL.ST.satisfies_pure in H4; PropXTac.propxFo ]
    end.

    destruct (exprD funcs uvars vars pe pcT); eauto.

    repeat match goal with
             | [ H : context [ match applyD ?A ?B ?C ?D ?E with
                                 | Some _ => _
                                 | None => _ 
                               end ] |- _ ] =>
               generalize dependent H; case_eq (applyD A B C D E); intros; intuition
             | [ H : SepIL.ST.satisfies _ (SepIL.ST.inj _) _ _ |- _ ] =>
               eapply SepIL.ST.satisfies_pure in H; PropXTac.propxFo; instantiate; intuition
           end.
    generalize dependent H8. case_eq (smem_write stn t v x2); intros; intuition.

    unfold smem_write in H8.
    pose (SepIL.ST.HT.join s0 x3).

    destruct (@SepIL.ST.HT.satisfies_set_word x4 m H5 (explode stn) t v (SepIL.ST.HT.join s0 x3)).
      destruct H7; subst.
      eapply SepIL.ST.HT.split_set_word in H8; eauto.
      intuition eauto.

       
    destruct H12. eexists; split; eauto.
    eexists; split; [ | eauto ].

    rewrite SEP.sheapD_pull_impure by eapply FM.find_add.
    rewrite SEP.starred_In. rewrite <- SEP.heq_star_assoc.
    rewrite SEP.heq_star_comm.

    simpl.
    eapply SepIL.ST.satisfies_star.

    rewrite H2. simpl in H3. rewrite H3. exists s0.
    exists x3. rewrite FM.remove_add. intuition.

    eapply SepIL.ST.HT.disjoint_split_join.

    eapply SepIL.ST.HT.split_set_word in H8.
    2: destruct H7; eauto.
    intuition eauto.
  Qed.

  Lemma symeval_read_word_correct' : forall hyps pe ve s,
    symeval_read_word hyps pe s = Some ve ->
    forall cs stn uvars vars m,
      AllProvable funcs uvars vars hyps ->
      (exists sm, 
        SepIL.ST.satisfies cs (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s)) stn sm
        /\ SepIL.ST.HT.satisfies sm m) ->
      match exprD funcs uvars vars pe pcT, exprD funcs uvars vars ve pcT with
        | Some p , Some v =>
          mem_get_word _ _  footprint_w SepIL.BedrockHeap.mem_get (IL.implode stn) p m = Some v
        | _ , _ => False
      end.
  Proof.
    unfold symeval_read_word. intros.
    eapply fold_known_correct in H.
    do 5 destruct H. destruct H1.
    intuition. 

    generalize (SEP.sheapD_pures _ _ _ _ _ H); intros.

    eapply SEP.sheapD_pull_impure 
      with (funcs := funcs) (sfuncs := sfuncs) (a := uvars) (c := vars) (cs := cs)
        in H1.
    apply In_split in H3. destruct H3. destruct H3.
    subst. 
    rewrite SEP.starred_In with (x := x3) (ls := x5) (ls' := x6) in H1.

    rewrite <- SEP.heq_star_assoc in H1. rewrite SEP.heq_star_comm in H1.
    rewrite H1 in H.
    simpl in H.
    rewrite H2 in *.
    eapply SepIL.ST.satisfies_star in H. destruct H. destruct H. intuition.
    
    eapply PLUGIN.sym_read_correct 
      with (uvars := uvars) (vars := vars) (cs := cs) (stn := stn) (m := x2)
        in H6.
    2: eapply AllProvable_app; auto.
    destruct (exprD funcs uvars vars pe pcT); auto.
    destruct (exprD funcs uvars vars ve pcT); auto.

    eapply SepIL.ST.HT.satisfies_get_word; eauto.
    eapply SepIL.ST.HT.split_smem_get_word; eauto.

    unfold tvarD. simpl.
    match goal with 
      | [ |- context [ applyD ?A ?B ?C ?D ?E ] ] =>
        destruct (applyD A B C D E)
    end; auto.
    eapply SepIL.ST.satisfies_pure in H. PropXTac.propxFo.
  Qed.
*)
  Lemma memoryIn_satisfies : forall m, 
    SepIL.ST.HT.satisfies (memoryIn m) m.
  Proof.
    clear.
    unfold satisfies, memoryIn.  (* rewrite SepIL.AllWords.memoryIn_eq.
    unfold SepIL.memoryIn_def, mem, smem, W, SepIL.allWords_def, SepIL.BedrockHeap.all_addr in *.
    intros.
    match goal with
      | [ |- context [ match ?X with 
                         | refl_equal => _
                       end ] ] => generalize X
    end.
    intro. generalize e. rewrite <- e.
    uip_all.
    clear.
    induction (pow2 32).
      compute; trivial.

      split;
        unfold SepIL.BedrockHeap.mem_get, SepIL.BedrockHeap.mem_acc, ReadByte.
      destruct (m $ n); split; try eexists; reflexivity.
      eauto.
 *)
  Admitted.

  Lemma satisfies_defn : forall cs se stn st,
    PropX.interp cs (SepIL.SepFormula.sepFormula se (stn, st)) ->
    (   SepIL.ST.satisfies cs se stn (memoryIn (Mem st))
     /\ SepIL.ST.HT.satisfies (memoryIn (Mem st)) (Mem st)).
  Proof.
    rewrite SepIL.SepFormula.sepFormula_eq in *. unfold SepIL.sepFormula_def.
    intros. destruct st; simpl in *. 
      unfold SepIL.ST.HT.satisfies, SepIL.memoryIn, memoryIn, ST.satisfies in *.
      intuition.
(*      eapply memoryIn_satisfies.
  Qed.*)
    Admitted.

  
  Lemma pures_implied : forall uvars vars0 specs stn s0 ss,
    PropX.interp specs
    (SepIL.SepFormula.sepFormula
      (SEP.sexprD funcs sfuncs uvars vars0 (SEP.sheapD ss))
      (stn, s0)) ->
    AllProvable funcs uvars vars0 (pures ss).
  Proof.
    intros.
    rewrite SepIL.SepFormula.sepFormula_eq in *.
    unfold SepIL.sepFormula_def in *. simpl in *.
    generalize SEP.sheapD_pures.
    unfold SepIL.ST.satisfies.
    intro. eapply (@H0 _ funcs _ _ sfuncs stn (SepIL.memoryIn (Mem s0)) specs
    uvars vars0).
    PropXTac.propxFo.
  Qed.

  Lemma symeval_read_word_correct : forall hyps pe ve s,
    symeval_read_word hyps pe s = Some ve ->
    forall cs stn uvars vars st p,
      exprD funcs uvars vars pe pcT = Some p ->
      AllProvable funcs uvars vars hyps ->
      PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s)) (stn, st)) ->
      match exprD funcs uvars vars ve pcT with
        | Some v =>
          mem_get_word _ _  footprint_w SepIL.BedrockHeap.mem_get (IL.implode stn) p (Mem st) = Some v
        | _ => False
      end.
  Proof.
    unfold symeval_read_word. intros.
    eapply fold_known_correct in H.
    do 5 destruct H. intuition.

    assert (AllProvable funcs uvars vars (pures s)). eapply pures_implied; eauto.

    eapply SEP.sheapD_pull_impure 
      with (funcs := funcs) (sfuncs := sfuncs) (a := uvars) (c := vars) (cs := cs)
        in H.
    rewrite H in H2.
    apply In_split in H4. destruct H4. destruct H4. subst.
    rewrite SEP.starred_In with (x := x3) (ls := x4) (ls' := x5) in H2.

    rewrite <- SEP.heq_star_assoc in H2. rewrite SEP.heq_star_comm in H2.
    simpl in H2. rewrite H3 in H2.
    eapply satisfies_defn in H2. intuition.
    eapply SepIL.ST.satisfies_star in H4. destruct H4. destruct H2. intuition.

    eapply PLUGIN.sym_read_correct with (uvars := uvars) (vars := vars) (cs := cs) (stn := stn) (m := x2) in H6; eauto.
      destruct (exprD funcs uvars vars ve pcT); auto.
      eapply SepIL.ST.HT.satisfies_get_word; eauto.
      eapply SepIL.ST.HT.split_smem_get_word; eauto.

      eapply AllProvable_app; eauto.

      simpl in *.
      match goal with
        | [ |- match ?X with
                 | Some _ => _
                 | None => _
               end ] => destruct X
      end; eauto.
      unfold ST.satisfies in H2. PropXTac.propxFo.
  Qed.

  Theorem symeval_write_word_correct : forall hyps pe ve s s',
    symeval_write_word hyps pe ve s = Some s' ->
    forall cs stn uvars vars st p v,
      exprD funcs uvars vars pe pcT = Some p ->
      exprD funcs uvars vars ve pcT = Some v ->
      AllProvable funcs uvars vars hyps ->
      PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s)) (stn, st)) ->
      match mem_set_word _ _ footprint_w SepIL.BedrockHeap.mem_set (IL.explode stn) p v (Mem st) with
        | Some m' => 
          PropX.interp cs 
          (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s')) 
            (stn, {| Regs := Regs st ; Mem := m' |}))
        | None => False
      end.
  Proof.
    unfold symeval_write_word; intros.
    assert (AllProvable funcs uvars vars (pures s)). eapply pures_implied; eauto.
    repeat match goal with
             | [ H : match ?X with 
                       | Some _ => _
                       | None => _
                     end = Some _ |- _ ] => revert H; case_eq X; try congruence; intros
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             | [ H : @fold_known_update _ _ _ _ _ _ _ _ = Some _ |- _ ] => 
               eapply fold_known_update_correct in H        
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H; subst
             | [ H : @fold_args_update _ _ _ _ _ _ _ = _ |- _ ] =>
               eapply fold_args_update_correct in H
           end.
    eapply SEP.sheapD_pull_impure 
      with (funcs := funcs) (sfuncs := sfuncs) (a := uvars) (c := vars) (cs := cs)
        in H5.
    rewrite H5 in H3. clear H5.
    rewrite SEP.starred_In with (x := x6) (ls := x4) (ls' := x5) in H3.
    rewrite <- SEP.heq_star_assoc in H3. rewrite SEP.heq_star_comm in H3.

    simpl in *. rewrite H in *. eapply satisfies_defn in H3. destruct H3.
    eapply SepIL.ST.satisfies_star in H3. destruct H3. destruct H3. intuition.

    eapply PLUGIN.sym_write_correct with (uvars := uvars) (vars := vars) (cs := cs) (stn := stn) (m := x2) in H6; eauto.
      2: eapply AllProvable_app; eauto.
      Focus 2.
      simpl in *.
      match goal with
        | [ |- match ?X with 
                 | Some _ => _
                 | None => _
               end ] => destruct X; auto
      end.
      unfold ST.satisfies in *. PropXTac.propxFo.

      
      repeat match goal with
               | [ H : match ?X with
                         | Some _ => _
                         | None => False
                       end |- _ ] => revert H; case_eq X; [ | intros; exfalso; assumption ]; intros
             end.
      unfold smem_write in *.
      generalize (satisfies_set_word (join x2 x3) (Mem st)).
      assert (disjoint x2 x3). destruct H7; auto.

      generalize (split_set_word _ _ H11 _ _ _ _ H8). intuition.
      eapply H13 in H15. destruct H15. intuition.
        unfold BedrockHeap.mem, footprint_w, BedrockHeap.footprint_w, BedrockHeap.addr in *.
        rewrite H15.

        rewrite SEP.sheapD_pull_impure with (f := x). simpl pures; simpl impures; simpl other.
        rewrite FM.remove_add. instantiate (1 := x4 ++ x7 :: x5).
        2: simpl; rewrite FM.find_add; auto.
        
        rewrite SEP.starred_In. rewrite <- SEP.heq_star_assoc. rewrite SEP.heq_star_comm.
        simpl. rewrite H. simpl in H6; rewrite H6. clear H13.
 
      match goal with
        | [ H : ST.satisfies _ ?X _ x3 |- _ ] =>
          generalize dependent X
      end; intros.

      (** BREAKS ABSTRACTION **)
      rewrite SepIL.SepFormula.sepFormula_eq. unfold sepFormula_def. simpl.
      unfold star.
      eapply PropX.Exists_I. instantiate (1 := s0).
      eapply PropX.Exists_I. instantiate (1 := x3).
      PropXTac.propxFo. split; eauto.
      generalize dependent s0. generalize dependent x8. generalize dependent x3. clear.
      intros.
      destruct H7. unfold satisfies in *.

      eapply relevant_eq; eauto.
      2: eapply memoryIn_satisfies.

      


      Focus 2.
      destruct H7.
(*      rewrite <- H12. eapply memoryIn_satisfies. *)


  Admitted.

  (** Symbolic State **)
  Record SymState : Type :=
  { SymMem  : SEP.SHeap types pcT stT
  ; SymRegs : SymRegType
  }.

  (** This has to be connected to the type of the intermediate representation **)
  Definition sym_evalLoc (lv : sym_loc types) (ss : SymState) : expr types :=
    match lv with
      | SymReg r => sym_getReg r (SymRegs ss)
      | SymImm l => l
      | SymIndir r w => fPlus (sym_getReg r (SymRegs ss)) w
    end.

  Definition sym_evalLval (lv : sym_lvalue types) (val : expr types) (ss : SymState) : option SymState :=
    match lv with
        | SymLvReg r =>
          Some {| SymMem := SymMem ss ; SymRegs := sym_setReg r val (SymRegs ss) |}
        | SymLvMem l => 
          let l := sym_evalLoc l ss in
          match symeval_write_word (pures (SymMem ss)) l val (SymMem ss) with
            | Some m =>
              Some {| SymMem := m ; SymRegs := SymRegs ss |}
            | None => None
          end
    end.

  Definition sym_evalRval (rv : sym_rvalue types) (ss : SymState) : option (expr types) :=
    match rv with
      | SymRvLval (SymLvReg r) =>
        Some (sym_getReg r (SymRegs ss))
      | SymRvLval (SymLvMem l) =>
        let l := sym_evalLoc l ss in
        symeval_read_word (pures (SymMem ss)) l (SymMem ss)
      | SymRvImm w => Some w 
      | SymRvLabel l => None (* TODO: can we use labels? it seems like we need to reflect these as words. *)
        (* an alternative would be to reflect these as a function call that does the positioning...
         * - it isn't clear that this can be done since the environment would need to depend on the settings.
         *)
        (*Some (Expr.Const (types := types) (t := tvType 2) l) *)
    end.

  Definition sym_evalInstr (i : sym_instr types) (ss : SymState) : option SymState :=
    match i with 
      | SymAssign lv rv =>
        match sym_evalRval rv ss with
          | None => None
          | Some rv => sym_evalLval lv rv ss
        end
      | SymBinop lv l o r =>
        match sym_evalRval l ss , sym_evalRval r ss with
          | Some l , Some r => 
            let v :=
              match o with
                | Plus  => fPlus
                | Minus => fMinus
                | Times => fMult
              end l r
            in
            sym_evalLval lv v ss
          | _ , _ => None
        end
    end.

  Fixpoint sym_evalInstrs (is : list (sym_instr types)) (ss : SymState) : SymState + (SymState * list (sym_instr types)) :=
    match is with
      | nil => inl ss
      | i :: is => match sym_evalInstr i ss with
                     | None => inr (ss, i :: is)
                     | Some ss => sym_evalInstrs is ss
                   end
    end.

  Variable resolveCond : forall (hyps : list (expr types)) (l : expr types) (tst : test) (r : expr types), option bool.

  Fixpoint sym_evalJmp (j : sym_jmp types) (ss : SymState) : option (SymState * list (list (expr types) * expr types)) :=
    match j with
      | SymUncond rv => match sym_evalRval rv ss with
                          | None => None
                          | Some v => Some (ss, (nil, v) :: nil)
                        end
      | SymCond rvl tst rvr l1 l2 =>
        match sym_evalRval rvl ss , sym_evalRval rvr ss with
          | Some l, Some r =>
            match resolveCond (pures (SymMem ss)) l tst r with
              | Some true => None (* Some (ss, (nil, @Expr.Const types pcT l1)) *)
              | Some false => None (* Some (ss, (nil, @Expr.Const types pcT l1)) *)
              | None => None (* Some (ss, (nil, @Expr.Const types pcT l1)) *)
            end
          | _ , _ => None
        end
    end.

  (* Denotation functions *)
  Section sym_denote.
    Variable uvars vars : env types.

    Definition sym_regsD (rs : SymRegType) : option regs :=
      match rs with
        | (sp, rp, rv) =>
          match 
            exprD funcs uvars vars sp tvWord ,
            exprD funcs uvars vars rp tvWord ,
            exprD funcs uvars vars rv tvWord 
            with
            | Some sp , Some rp , Some rv =>
                Some (fun r => 
                  match r with
                    | Sp => sp
                    | Rp => rp
                    | Rv => rv
                  end)
            | _ , _ , _ => None
          end
      end.    

    Definition sym_locD (s : sym_loc types) : option loc :=
      match s with
        | SymReg r => Some (Reg r)
        | SymImm e =>
          match exprD funcs uvars vars e tvWord with
            | Some e => Some (Imm e)
            | None => None
          end
        | SymIndir r o =>
          match exprD funcs uvars vars o tvWord with
            | Some o => Some (Indir r o)
            | None => None
          end
      end.

    Definition sym_lvalueD (s : sym_lvalue types) : option lvalue :=
      match s with
        | SymLvReg r => Some (LvReg r)
        | SymLvMem l => match sym_locD l with
                          | Some l => Some (LvMem l)
                          | None => None
                        end
      end.

    Definition sym_rvalueD (r : sym_rvalue types) : option rvalue :=
      match r with
        | SymRvLval l => match sym_lvalueD l with
                           | Some l => Some (RvLval l)
                           | None => None
                         end
        | SymRvImm e => match exprD funcs uvars vars e tvWord with
                          | Some l => Some (RvImm l)
                          | None => None
                        end
        | SymRvLabel l => Some (RvLabel l)
      end.

    Definition sym_instrD (i : sym_instr types) : option instr :=
      match i with
        | SymAssign l r =>
          match sym_lvalueD l , sym_rvalueD r with
            | Some l , Some r => Some (Assign l r)
            | _ , _ => None
          end
        | SymBinop lhs l o r =>
          match sym_lvalueD lhs , sym_rvalueD l , sym_rvalueD r with
            | Some lhs , Some l , Some r => Some (Binop lhs l o r)
            | _ , _ , _ => None
          end
      end.

    Fixpoint sym_instrsD (is : list (sym_instr types)) : option (list instr) :=
      match is with
        | nil => Some nil
        | i :: is => 
          match sym_instrD i , sym_instrsD is with
            | Some i , Some is => Some (i :: is)
            | _ , _ => None
          end
      end.

    Require Import PropX.

    Definition stateD cs (stn : IL.settings) (s : state) (ss : SymState) : Prop :=
      match ss with
        | {| SymMem := m ; SymRegs := (sp, rp, rv) |} =>
          match 
             exprD funcs uvars vars sp tvWord ,
             exprD funcs uvars vars rp tvWord ,
             exprD funcs uvars vars rv tvWord  with
            | Some sp , Some rp , Some rv =>
              Regs s Sp = sp /\ Regs s Rp = rp /\ Regs s Rv = rv
            | _ , _ , _ => False
          end
          /\ PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD m)) (stn, s))%PropX
      end.

  End sym_denote.

  Ltac sound_simp :=
    repeat match goal with 
             | [ H : False |- _ ] => inversion H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ = _ |- _ ] => 
               rewrite H
             | [ H : match ?X with
                       | {| SymMem := _ ; SymRegs := _ |} => _
                     end |- _ ] =>
             destruct X
             | [ H : match ?X with
                       | (_, _) => _
                     end |- _ ] =>
             destruct X
             | [ H : match ?X with
                       | Some _ => _
                       | None => _
                     end |- _ ] =>
             generalize dependent H; case_eq X; intros; try congruence; simpl in *
             | [ H : match ?X with
                       | Some _ => _
                       | None => _
                     end = _ |- _ ] =>
             generalize dependent H; case_eq X; intros; try congruence; simpl in *
             | [ H : match ?X with
                       | SymLvReg _ => _
                       | SymLvMem _ => _
                     end = _ |- _ ] =>
             generalize dependent H; case_eq X; intros; try congruence; simpl in *
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst; simpl in *
             | [ |- exists x, _ /\ Some _ = Some x ] =>
               eexists; split; [ | reflexivity ]
           end; simpl.

  Lemma sym_getReg_sound : forall stn specs uvars vars r ss s,
    stateD uvars vars specs stn s ss ->
    exprD funcs uvars vars (sym_getReg r (SymRegs ss)) tvWord = Some (Regs s r).
  Proof.
    destruct ss; simpl in *; intros. 
    sound_simp; intuition; subst. destruct r; simpl; auto.
  Qed.

  Lemma sym_loc_sound : forall uvars vars l lD,
    sym_locD uvars vars l = Some lD ->
    forall specs stn s ss, 
      stateD uvars vars specs stn s ss ->
      forall a,
        sym_evalLoc l ss = a ->
        exprD funcs uvars vars a tvWord = Some (evalLoc s lD).
  Proof.
    destruct l; intros; subst; simpl in *; sound_simp; eauto.
    erewrite sym_getReg_sound by eauto. reflexivity.
    generalize (fPlus_correct (sym_getReg r (SymRegs ss)) e uvars vars).
    rewrite H.
    erewrite sym_getReg_sound by eauto; auto.
  Qed.

  Lemma sym_lvalue_safe : forall uvars vars0 l lD,
    sym_lvalueD uvars vars0 l = Some lD ->
    forall specs stn s ss, 
      stateD uvars vars0 specs stn s ss ->
      forall a aD ss',
        exprD funcs uvars vars0 a tvWord = Some aD ->
        sym_evalLval l a ss = Some ss' ->
        exists s' , 
          evalLvalue stn s lD aD = Some s'
          /\ stateD uvars vars0 specs stn s' ss'.
  Proof.
    destruct l; simpl; intros; try congruence.
    inversion H; clear H; subst.
    inversion H2; clear H2; subst.
    simpl; eexists; split; [ reflexivity | ].
    destruct ss; destruct SymRegs0; destruct p.
    simpl in H0. intuition.
    rewrite SepIL.SepFormula.sepFormula_eq in *.
    unfold SepIL.sepFormula_def in *. simpl in *.
    destruct r; unfold rupd; simpl; 
      intuition; sound_simp; intuition; subst.

    repeat match goal with
             | [ H : match ?X with 
                       | Some _ => _
                       | None => _
                     end = Some _ |- _ ] => 
               revert H; case_eq X; intros; try congruence
             | [ H : Some _ = Some _ |- _ ] => 
               inversion H; clear H; subst
           end.
    eapply sym_loc_sound in H; eauto.
    eapply symeval_write_word_correct in H2; eauto;
      unfold stateD in *; PropXTac.propxFo.
    Focus 2.
    rewrite SepIL.SepFormula.sepFormula_eq in *.
    unfold SepIL.sepFormula_def in *. simpl in *.
    destruct ss; destruct SymRegs0; destruct p; intuition.
    generalize pures_implied. rewrite SepIL.SepFormula.sepFormula_eq. simpl. unfold sepFormula_def. simpl. eauto.

(*
    admit.

    sound_simp.
    unfold WriteWord. unfold BedrockHeap.mem_set in H4.
    unfold pcT, tvWord in *. eauto. rewrite H in H2. inversion H2; clear H2; subst.
    rewrite H4.
    eexists; intuition. 
*)
  Admitted.

  Lemma sym_lvalue_sound : forall uvars vars0 l lD,
    sym_lvalueD uvars vars0 l = Some lD ->
    forall specs stn s ss, 
      stateD uvars vars0 specs stn s ss ->
      forall a aD ss',
        exprD funcs uvars vars0 a tvWord = Some aD ->
        sym_evalLval l a ss = Some ss' ->
        forall s' , 
          evalLvalue stn s lD aD = Some s' ->
          stateD uvars vars0 specs stn s' ss'.
  Proof.
    destruct l; simpl; intros; try congruence.
      sound_simp; destruct ss; destruct SymRegs0; destruct p; simpl in *.
      revert H0. unfold stateD. rewrite sepFormula_eq. unfold sepFormula_def. simpl.
      intros. destruct r; simpl; sound_simp; subst; intuition.

(*
      sound_simp.
      eapply sym_loc_sound in H; eauto.
      eapply symeval_write_word_correct in H2; eauto;
        unfold stateD in H0; 
      destruct ss; destruct SymRegs0; destruct p; simpl in *; intuition eauto.
      simpl in *.      
      sound_simp; subst.
      unfold WriteWord in H3. unfold pcT, tvWord in *. rewrite H in *. sound_simp.
      unfold BedrockHeap.mem_set in *. rewrite H3 in H10. sound_simp. auto.
  Qed.
*)
  Admitted.

  Lemma sym_rvalue_sound : forall uvars vars0 r rD,
    sym_rvalueD uvars vars0 r = Some rD ->
    forall specs stn s ss, 
      stateD uvars vars0 specs stn s ss ->
      forall rv,
        sym_evalRval r ss = Some rv ->
        exists rvD ,
          exprD funcs uvars vars0 rv tvWord = Some rvD /\
          evalRvalue stn s rD = Some rvD.
  Proof.
    destruct r; simpl; intros.
      destruct s; sound_simp. 
        erewrite sym_getReg_sound; eauto.

        Focus.
        generalize (sym_loc_sound _ _ _ _ H _ _ _ _ H0 _ (refl_equal _)); intros.
        eapply symeval_read_word_correct with (vars := vars0) (uvars := uvars) 
          (cs := specs) (stn := stn) (st := s0) in H1; eauto.
                unfold ReadWord, SepIL.BedrockHeap.mem_get in *.
        unfold pcT, tvWord in *.
        destruct (exprD funcs uvars vars0 rv (tvType 0)); intuition.
        eexists; intuition eauto.

        unfold stateD in *. sound_simp. subst. intuition.

        Focus.
        sound_simp; auto.

        Focus. (* congruence *)
 Admitted.

  Lemma sym_binops : forall uvars vars0 b e e0 x x0,
    exprD funcs uvars vars0 e tvWord = Some x ->
    exprD funcs uvars vars0 e0 tvWord = Some x0 ->
    exprD funcs uvars vars0
    (match b with
       | Plus => fPlus
       | Minus => fMinus
       | Times => fMult
     end e e0) tvWord = Some (evalBinop b x x0).
  Proof.
    destruct b; simpl; intros.
      generalize (fPlus_correct e e0 uvars vars0); rewrite H; rewrite H0; auto.
      generalize (fMinus_correct e e0 uvars vars0); rewrite H; rewrite H0; auto.
      generalize (fMult_correct e e0 uvars vars0); rewrite H; rewrite H0; auto.
  Qed.
    
  Theorem sym_evalInstr_safe : forall i iD uvars vars, 
    sym_instrD uvars vars i = Some iD ->
    forall stn ss ss',
    sym_evalInstr i ss = Some ss' ->
    forall specs s,
    stateD uvars vars specs stn s ss ->
    exists s',
    evalInstr stn s iD = Some s' /\ stateD uvars vars specs stn s' ss'.
  Proof.
    destruct i; simpl; intros iD uvars vars0.

      intros; sound_simp; try congruence.
      eapply sym_rvalue_sound in H3; eauto.
      destruct H3. intuition.
      eapply sym_lvalue_safe in H2; eauto.
      destruct H2; intuition.
      rewrite H5. eauto.

      intros; sound_simp; try congruence.
      eapply sym_rvalue_sound in H0; eauto.
      eapply sym_rvalue_sound in H2; eauto.
      destruct H0; destruct H2; intuition.
      rewrite H7. rewrite H8.
      
      eapply sym_lvalue_safe in H3; eauto.
      eapply sym_binops; eauto.
  Qed.

  Theorem sym_evalInstrs_safe : forall uvars vars cs sym_instrs instrs stn st ss, 
      stateD uvars vars cs stn st ss ->
      sym_instrsD uvars vars sym_instrs = Some instrs ->
      match sym_evalInstrs sym_instrs ss with
        | inl ss' =>
          exists st',
               evalInstrs stn st instrs = Some st'
            /\ stateD uvars vars cs stn st' ss'
        | inr (ss'', is') =>
          exists st'', 
            match sym_instrsD uvars vars is' with
              | None => False 
              | Some instrs' =>
                   evalInstrs stn st instrs = evalInstrs stn st'' instrs'
                /\ stateD uvars vars cs stn st'' ss''
            end
      end.
  Proof.
    clear. induction sym_instrs; simpl; intros; sound_simp; auto.
      eexists; eauto.
    
    case_eq (sym_evalInstr a ss); intros.
      eapply sym_evalInstr_safe in H0; eauto.
      destruct H0. intuition. sound_simp.

      eapply IHsym_instrs in H4; eauto.
      simpl. sound_simp.
      eexists; split; try reflexivity. auto.
  Qed.

  Theorem sym_evalInstrs_sound : forall i iD uvars vars, 
    sym_instrsD uvars vars i = Some iD ->
    forall stn ss ss',
      sym_evalInstrs i ss = inl ss' ->
      forall specs s,
        stateD uvars vars specs stn s ss ->
        evalInstrs stn s iD = None ->
        False.
  Proof.
    induction i; simpl; intros.
      sound_simp; congruence.

      sound_simp;
      eapply sym_evalInstr_safe in H; eauto;
      destruct H; intuition;
      repeat (match goal with
                | [ H : ?X = _ , H' : ?X = _ |- _ ] =>
                  rewrite H in H'
              end; sound_simp); try congruence.
      eapply IHi; eauto.
  Qed.

  Require Import PropX.

  Fixpoint existsAll (ls : variables) (F : env types -> Prop) : Prop := 
    match ls with 
      | nil => F nil
      | l :: ls => 
        existsAll ls (fun g => exists x, F (x :: g))
    end.

  Lemma hash_interp : forall sfuncs se sh,
    SEP.hash se = (nil, sh) ->
    forall uvars vars st stn cs,
    PropX.interp cs (![ @SEP.sexprD types funcs pcT stT sfuncs uvars vars se ] (stn, st)) ->
    PropX.interp cs (![ @SEP.sexprD types funcs pcT stT sfuncs uvars vars (SEP.sheapD sh) ] (stn, st)).
  Proof.
    clear. intros.
    generalize (SEP.hash_denote funcs sfuncs cs se uvars vars).
    rewrite H. simpl. intros.
    rewrite <- H1. eauto.
  Qed.

  (** TODO: add pures to this! **)
  Theorem sym_evalInstrs_safe_apply : forall uvars vars cs instrs stn st,
    evalInstrs stn st instrs = None ->
    forall sp rv rp sh,
      PropX.interp cs 
        (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars sh) (stn, st)%PropX) ->
      exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
      exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
      exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
    forall hashed,
      (** TODO: is this a bad restriction? **)
      SEP.hash sh = (nil , hashed) ->
      forall sym_instrs,
        sym_instrsD uvars vars sym_instrs = Some instrs ->
        match sym_evalInstrs sym_instrs 
          {| SymRegs := (sp, rp, rv) ; SymMem  := hashed |} 
          with
          | inl ss' => False 
          | inr (ss'', is') =>
            exists st'', 
              match sym_instrsD uvars vars is' with
                | None => False 
                | Some instrs' =>
                     evalInstrs stn st'' instrs' = None
                  /\ stateD uvars vars cs stn st'' ss''
              end
        end.
  Proof.  
    clear; intros.
    eapply sym_evalInstrs_safe with 
      (ss := {| SymRegs := (sp, rp, rv) ; SymMem := hashed |})
      (stn := stn) (cs := cs) (st := st) in H5; eauto.
    match goal with
      | [ |- match ?X with 
               | inl _ => _
               | inr _ => _
             end ] => destruct X
    end.
    destruct H5; intuition. rewrite H in H6; congruence.
    rewrite <- H. destruct p. destruct H5. exists x.
    sound_simp. intuition. rewrite <- H6. eauto.

    unfold stateD. sound_simp. intuition eauto.
    eapply hash_interp; eauto.
  Qed.

  Theorem sym_evalInstrs_sound_apply : forall uvars vars cs instrs stn st st', 
    evalInstrs stn st instrs = Some st' ->
    forall sp rv rp sh,
      PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars sh) (stn, st)%PropX) ->
      exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
      exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
      exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
    forall hashed,
      (** TODO: is this a bad restriction? **)
      SEP.hash sh = (nil , hashed) ->
      forall sym_instrs,
        sym_instrsD uvars vars sym_instrs = Some instrs ->
        match sym_evalInstrs sym_instrs 
          {| SymRegs := (sp, rp, rv) ;
            SymMem  := hashed |} with
          | inl ss' =>
            stateD uvars vars cs stn st' ss'
          | inr (ss'', is') =>
            exists st'', 
              match sym_instrsD uvars vars is' with
                | None => False 
                | Some instrs' =>
                     evalInstrs stn st'' instrs' = Some st'
                  /\ stateD uvars vars cs stn st'' ss''
              end
        end.
  Proof.
    clear; intros.
    eapply sym_evalInstrs_safe with (stn := stn) (cs := cs) 
      (ss := {| SymRegs := (sp, rp, rv) ; SymMem := hashed |}) in H5; eauto.
    2: unfold stateD; sound_simp; intuition eauto;
    eapply hash_interp; eauto.
    match goal with 
      | [ |- match ?X with 
               | inl _ => _
               | inr _ => _
             end ] => destruct X
    end; try rewrite H in *.
    destruct H5; sound_simp; eauto.
    destruct p. destruct H5. exists x.
    sound_simp. intuition; eauto.
  Qed.

  Theorem sym_evalInstrs_any_apply : forall (uvars vars : list {t : Expr.tvar & Expr.tvarD types t})
    (sp rv rp : Expr.expr types)  (st : state),
    @Expr.exprD types funcs uvars vars sp tvWord = @Some W (Regs st Sp) ->
    @Expr.exprD types funcs uvars vars rv tvWord = @Some W (Regs st Rv) ->
    @Expr.exprD types funcs uvars vars rp tvWord = @Some W (Regs st Rp) ->
    forall (hashed : SEP.SHeap types pcT stT)
      (cs : codeSpec W (settings * state)) (stn : settings),
      @interp W (settings * state) cs (![@SEP.sexprD types funcs pcT stT sfuncs uvars vars (SEP.sheapD hashed)] (stn, st)) ->
    forall (sym_instrs : list (sym_instr types)) (instrs : list instr),
      @sym_instrsD uvars vars sym_instrs = @Some (list instr) instrs ->
    forall some_or_none,
      evalInstrs stn st instrs = some_or_none ->
      match some_or_none with
        | None =>
          match
            @sym_evalInstrs sym_instrs {| SymMem := hashed; SymRegs := (sp, rp, rv) |}
            with
            | inl _ => False
            | inr (ss'', is') =>
              exists st'' : state,
                match @sym_instrsD uvars vars is' with
                  | Some instrs' =>
                    evalInstrs stn st'' instrs' = @None state /\
                    @stateD uvars vars cs stn st'' ss''
                  | None => False
                end
          end
        | Some st' =>
          match
            @sym_evalInstrs sym_instrs {| SymMem := hashed; SymRegs := (sp, rp, rv) |}
            with
            | inl ss' => @stateD uvars vars cs stn st' ss'
            | inr (ss'', is') =>
              exists st'' : state,
                match @sym_instrsD uvars vars is' with
                  | Some instrs' =>
                    evalInstrs stn st'' instrs' = @Some state st' /\
                    @stateD uvars vars cs stn st'' ss''
                  | None => False
                end
          end
      end.
  Proof.
    intros. destruct some_or_none.
      eapply sym_evalInstrs_sound_apply with (hashed := hashed); eauto. admit.
      eapply sym_evalInstrs_safe_apply with (hashed := hashed); eauto. admit.
  Qed.

  End typed_ext.

  (* Reflect the instructions *)
  Ltac collectTypes_loc isConst l Ts :=
    match l with
      | Reg _ => Ts
      | Imm ?i => SEP.collectTypes_expr isConst i Ts
      | Indir _ ?i => SEP.collectTypes_expr isConst i Ts
    end.
  Ltac reflect_loc isConst l types funcs uvars vars k :=
    match l with
      | Reg ?r => constr:(@SymReg types r)
      | Imm ?i =>
        SEP.reflect_expr isConst i types funcs uvars vars ltac:(fun funcs i =>
          let l := constr:(@SymImm types i) in k funcs l)
      | Indir ?r ?i =>
        SEP.reflect_expr isConst i types funcs uvars vars ltac:(fun funcs i =>
          let l := constr:(@SymIndir types r i) in k funcs l)
    end.

  Ltac collectTypes_lvalue isConst l Ts :=
    match l with
      | LvReg _ => Ts
      | LvMem ?l => collectTypes_loc isConst l Ts
    end.
  Ltac reflect_lvalue isConst l types funcs uvars vars k :=
    match l with
      | LvReg ?r => let l := constr:(@SymLvReg types r) in k funcs l 
      | LvMem ?l => 
        reflect_loc isConst l types funcs uvars vars ltac:(fun funcs l =>
          let l := constr:(@SymLvMem types l) in k funcs l)
    end.

  Ltac collectTypes_rvalue isConst r Ts :=
    match r with
      | RvLval ?l => collectTypes_lvalue isConst l Ts
      | RvImm ?i => SEP.collectTypes_expr isConst i Ts
      | RvLabel _ => let l := constr:(label:Type) in Reflect.cons_uniq l Ts
    end.
  Ltac reflect_rvalue isConst r types funcs uvars vars k :=
    match r with
      | RvLval ?l =>
        reflect_lvalue isConst l types funcs uvars vars ltac:(fun funcs l =>
          let l := constr:(@SymRvLval types l) in k funcs l)
      | RvImm ?i =>
        SEP.reflect_expr isConst i types funcs uvars vars ltac:(fun funcs i =>
          let l := constr:(@SymRvImm types i) in k funcs l)
      | RvLabel ?l => 
        let r := constr:(@SymRvLabel types l) in k funcs r
    end.

  Ltac collectTypes_instr isConst i Ts :=
    match i with
      | Assign ?l ?r =>
        let Ts := collectTypes_lvalue isConst l Ts in
        collectTypes_rvalue isConst r Ts
      | Binop ?l ?r1 _ ?r2 =>
        let Ts := collectTypes_lvalue isConst l Ts in
        let Ts := collectTypes_rvalue isConst r1 Ts in
        collectTypes_rvalue isConst r2 Ts
    end.
  Ltac reflect_instr isConst i types funcs uvars vars k :=
    match i with
      | Assign ?l ?r =>
        reflect_lvalue isConst l types funcs uvars vars ltac:(fun funcs l =>
        reflect_rvalue isConst r types funcs uvars vars ltac:(fun funcs r =>
          let res := constr:(@SymAssign types l r) in k funcs res))
      | Binop ?l ?r1 ?o ?r2 =>
        reflect_lvalue isConst l types funcs uvars vars ltac:(fun funcs l =>
        reflect_rvalue isConst r1 types funcs uvars vars ltac:(fun funcs r1 =>
        reflect_rvalue isConst r2 types funcs uvars vars ltac:(fun funcs r2 =>
          let res := constr:(@SymBinop types l r1 o r2) in k funcs res)))
    end.

  Ltac collectTypes_instrs isConst is Ts :=
    match is with
      | nil => Ts
      | ?i :: ?is => 
        let Ts := collectTypes_instr isConst i Ts in
        collectTypes_instrs isConst is Ts
    end.
  Ltac reflect_instrs isConst is types funcs uvars vars k :=
    match is with
      | nil => 
        let is := constr:(@nil (sym_instr types)) in k funcs is
      | ?i :: ?is =>
        reflect_instr isConst i types funcs uvars vars ltac:(fun funcs i =>
        reflect_instrs isConst is types funcs uvars vars ltac:(fun funcs is =>
          let res := constr:(i :: is) in k funcs res))
    end.

  Ltac isConst e :=
    match e with
      | 0 => true
      | S ?e => isConst e
      | true => true
      | false => true
      | _ => false
    end.

  Ltac find_reg st r :=
    match goal with
      | [ H : Regs st r = ?x |- _ ] => x
      | _ => constr:((Regs st r, @refl_equal (option W) (Some (Regs st r))))
    end.

  Existing Class PLUGIN.SymEval.

  Ltac sym_evaluator H := 
    cbv beta iota zeta delta
      [ sym_evalInstrs sym_evalInstr sym_evalLval sym_evalRval sym_evalLoc
        symeval_read_word symeval_write_word 
        SymEval.fold_known SymEval.fold_args
        SymEval.fold_known_update SymEval.fold_args_update
        sym_setReg sym_getReg
        PLUGIN.sym_read PLUGIN.sym_write PLUGIN.Build_SymEval
        SepExpr.pures SepExpr.impures SepExpr.other
        SymMem SymRegs 
        SEP.star_SHeap SEP.liftSHeap SEP.multimap_join 
        Expr.SemiDec_expr Expr.expr_seq_dec Expr.tvar_val_sdec Expr.Eq Expr.liftExpr
        app map nth_error value error fold_right
        DepList.hlist_hd DepList.hlist_tl DepList.seq_dec 
        SepExpr.FM.find SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty SepExpr.FM.fold
        Compare_dec.lt_eq_lt_dec nat_rec nat_rect Peano_dec.eq_nat_dec sumbool_rec sumbool_rect
        EquivDec.equiv_dec EquivDec.nat_eq_eqdec
        f_equal 
        bedrock_funcs bedrock_types pcT stT tvWord
        fst snd
        types
      ] in H.

   Ltac denote_evaluator H :=
     cbv beta iota zeta delta
      [ stateD 
        Expr.exprD SEP.sexprD
        EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
        eq_rec_r eq_rec eq_rect eq_sym Logic.eq_sym
        funcs
        Expr.Range Expr.Domain Expr.Denotation Expr.tvarD Expr.applyD
        SEP.sheapD SEP.starred
        SepExpr.pures SepExpr.impures SepExpr.other
        Expr.Impl
        SepExpr.SDenotation SepExpr.SDomain
        tvWord pcT stT bedrock_types bedrock_funcs
        sumbool_rect sumbool_rec
        Peano_dec.eq_nat_dec
        nat_rec nat_rect
        nth_error types value error app fold_right
        SepExpr.FM.fold
        f_equal
      ] in H.

  Ltac build_evals sigs types' funcs' k :=
    let DF := constr:(fun n : nat => 
      match nth_error sigs n with
        | Some ss => 
          @PLUGIN.SymEval (types types') stT pcT pcT pcT smem_read smem_write
          (funcs types' funcs') ss
        | None => Empty_set
      end) in
    let rec build cur k :=
      let t := eval simpl in (nth_error sigs cur) in
      match t with
        | error => 
          let indicies := constr:(@nil nat) in
          let evals := constr:(@HNil nat DF) in
          k indicies evals
        | value ?s =>
          let n := constr:(S cur) in
          (* NOTE: This relies on type class resolution *)
          ((let x := constr:(_ : @PLUGIN.SymEval _ stT pcT pcT pcT _ _ (funcs types' funcs') s) in
            build n ltac:(fun is' ev' =>
              let is := constr:(cur :: is') in
              let ev := constr:(@HCons _ DF cur is' x ev') in
              k is ev)) || build n k)
      end
    in
    build 0 k.

  Lemma Some_inj : forall T (a b : T), a = b -> Some b = Some a.
  Proof.
    intros; subst; reflexivity.
  Qed.

  (** TODO:
   ** - To avoid reflecting for each basic block, I need to gather all the
   **   hypotheses and information that will go into the term at the beginning
   ** - The "algorithm" is:
   **   1) reflect everything!
   **   2) forward unfolding
   **   3) symbolic evaluation
   **   4) backward unfolding
   **   5) cancelation
   ** - steps 2-4 are repeated for each basic block that we evaluate
   ** NOTE: 
   ** - I don't know what Fs and SFs should be!
   **)
  Ltac sym_eval isConst Ts Fs SFs simplifier :=
    (** NOTE: This has two continuation for success and failure.
     ** success :: rp_v rp_pf sp_v sp_pf rv_v rv_pf SF sep_proof st -> ...
     ** failure :: st -> ...
     **)
    let rec symeval types_ext funcs_ext sfuncs knowns evals uvars vars 
      rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis SF sepFormula_pf success failure :=
      let rec continue rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis SH sepFormula_pf :=
        match sis with
          | tt => 
            success rp_v rp_pf sp_v sp_pf rv_v rv_pf SH sepFormula_pf st 
          | ((?is, ?sis, ?evalInstrs_pf), ?rem) =>
            apply (@sym_evalInstrs_any_apply types_ext funcs_ext sfuncs knowns evals
              uvars vars sp_v rv_v rp_v _ sp_pf rv_pf rp_pf SH (* cs *) _ (* stn *) _ sepFormula_pf
              sis is (refl_equal _)) in evalInstrs_pf;
            ((simplifier evalInstrs_pf ; sym_evaluator evalInstrs_pf) || fail 100 "simplification failed") ;
            let k := type of evalInstrs_pf in
            match k with
              | False => exfalso; exact evalInstrs_pf
              | @stateD _ _ _ _ _ _ _ _ (@Build_SymState _ ?M (?ssp, ?srp, ?srv)) =>
                denote_evaluator evalInstrs_pf ;
                match type of evalInstrs_pf with
                  | _ /\ PropX.interp _ (SepIL.SepFormula.sepFormula _ (_, ?st')) =>
                    clear sepFormula_pf ;
                    let regsD_pf := fresh in
                    let sepFormula_pf := fresh in
                    destruct evalInstrs_pf as [ regsD_pf sepFormula_pf ] ;
                    continue
                      srp (@Some_inj _ _ _ (proj1 (proj2 regsD_pf)))
                      ssp (@Some_inj _ _ _ (proj1 regsD_pf))
                      srv (@Some_inj _ _ _ (proj2 (proj2 regsD_pf)))
                      st' rem M sepFormula_pf 
                end
              | exists st'', _ =>
                let a := fresh in
                destruct evalInstrs_pf as [ a ? ] ;
                clear sepFormula_pf ;
                failure a 
            end
        end
      in
      continue rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis SF sepFormula_pf
    in
    let rec get_instrs st :=
      match goal with
        | [ H : evalInstrs _ st ?is = Some ?X |- _ ] =>
          let v := get_instrs X in
          constr:(((is, H), v))
        | [ H : evalInstrs _ st ?is = None |- _ ] =>
          constr:(((is, H), tt))
        | [ |- _ ] => tt
      end
    in
    let rec collectAllTypes_instrs is Ts :=
      match is with
        | tt => Ts
        | ((?i, _), ?is) =>
          let Ts := collectTypes_instrs ltac:(isConst) i Ts in
          collectAllTypes_instrs is Ts
      end
    in
    let rec reflect_all_instrs ais types funcs uvars vars k :=
      match ais with
        | tt => k funcs tt
        | ((?is, ?H), ?ais) =>
          reflect_instrs ltac:(isConst) is types funcs uvars vars ltac:(fun funcs sis =>
            let res := constr:((is, sis, H)) in
            reflect_all_instrs ais types funcs uvars vars ltac:(fun funcs sis => 
              let res := constr:((res, sis)) in
              k funcs res))
      end
    in
    let shouldReflect P :=
      match P with
        | evalInstrs _ _ _ = _ => false
        | @PropX.interp _ _ _ _ => false
        | @PropX.valid _ _ _ _ _ => false
        | @eq ?X _ _ => 
          match X with
            | context [ PropX.PropX ] => false
            | context [ PropX.spec ] => false
          end
        | forall x, _ => false
        | exists x, _ => false
        | _ => true
      end
    in
    let Ts :=
      match Ts with
        | tt => constr:(@nil Type)
        | _ => Ts
      end
    in
    match goal with
      | [ H : evalInstrs ?stn ?st ?is = ?R
        , H' : PropX.interp ?cs (SepIL.SepFormula.sepFormula ?SF (?stn, ?st)) |- _ ] =>
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
            match find_reg st Sp with
              | (?sp_v, ?sp_pf) =>
                match find_reg st Rv with
                  | (?rv_v, ?rv_pf) => 
                    let all_instrs := get_instrs st in
                    let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
                    (** collect the raw types **)
                    let Ts := collectAllTypes_instrs all_instrs Ts in
                    let Ts := SEP.collectAllTypes_expr ltac:(isConst) Ts regs in
                    let Ts := SEP.collectAllTypes_sexpr isConst Ts (SF :: nil) in
                    let Ts := SEP.collectAllTypes_funcs Ts Fs in
                    let Ts := SEP.collectAllTypes_sfuncs Ts SFs in
                    let Ts := SEP.collectAllTypes_props shouldReflect isConst Ts in
                    (** check for potential universe problems **)
                    match Ts with
                      | context [ PropX.PropX ] => 
                        fail 1000 "found PropX in types list"
                          "(this causes universe inconsistencies)"
                      | context [ PropX.spec ] => 
                        fail 1000 "found PropX in types list"
                          "(this causes universe inconsistencies)"
                      | _ => idtac
                    end;
                    (** elaborate the types **)
                    let types := eval unfold bedrock_types in bedrock_types in
                    let types := SEP.extend_all_types Ts types in
                    let types_ext := eval simpl in (bedrock_ext types) in 
                    (** build the base functions **)
                    let funcs := eval unfold bedrock_funcs in (bedrock_funcs types_ext) in
                    let funcs := SEP.getAllFunctions types funcs Fs in
                    let funcs := eval simpl in funcs in
                    (** build the base sfunctions **)
                    let sfuncs := constr:(@nil (@SEP.ssignature types pcT stT)) in
                    let sfuncs := SEP.getAllSFunctions pcT stT types sfuncs SFs in
                    let uvars := eval simpl in (@nil _ : Expr.env types) in
                    let vars := eval simpl in (@nil _ : Expr.env types) in
                    reflect_all_instrs all_instrs types funcs uvars vars ltac:(fun funcs sis =>
                    SEP.reflect_props shouldReflect ltac:(isConst) types funcs uvars vars ltac:(fun funcs pures proofs =>
                    SEP.reflect_expr ltac:(isConst) rp_v types funcs uvars vars ltac:(fun funcs rp_v =>
                    SEP.reflect_expr ltac:(isConst) sp_v types funcs uvars vars ltac:(fun funcs sp_v =>
                    SEP.reflect_expr ltac:(isConst) rv_v types funcs uvars vars ltac:(fun funcs rv_v =>
                    SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
                      match funcs with 
                        | _ :: _ :: _ :: ?funcs_ext =>
                          apply (@hash_interp types_ext funcs_ext sfuncs SF _ (refl_equal _) uvars vars) in H' ;
                          match type of H' with
                            | PropX.interp _ (![ @SEP.sexprD _ _ _ _ _ _ _ (SEP.sheapD ?SH) ] _) =>
                              (** TODO: I need to do something with [pures] **)
                              build_evals sfuncs types_ext funcs_ext ltac:(fun knowns evals =>
                                symeval types_ext funcs_ext sfuncs knowns evals uvars vars 
                                  rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis SH H'
                                  ltac:(fun rp_v rp_pf sp_v sp_pf rv_v rv_pf SH sep_proof st => idtac "succeeded")
                                  ltac:(fun _ => idtac "failed!"))
                          end
                    end))))))
                end
            end
        end
    end.

  Ltac simplifier H := idtac.

  Goal forall cs stn st st' SF,
    PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) ->
    evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' ->
    Regs st' Rp = natToW 0.
  Proof.
    intros. sym_eval ltac:(isConst) tt tt tt simplifier. simpl in *. intuition.
  Qed.

End BedrockEvaluator.

