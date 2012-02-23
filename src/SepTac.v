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
  :: SEP.defaultType (settings * state)%type
  :: SEP.defaultType label :: nil.

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

  Lemma satisfies_defn : forall cs se stn st,
    PropX.interp cs (SepIL.SepFormula.sepFormula se (stn, st)) <->
    (exists sm, 
         SepIL.ST.satisfies cs se stn sm
      /\ SepIL.ST.HT.satisfies sm (Mem st)).
  Proof.
    rewrite SepIL.SepFormula.sepFormula_eq in *. unfold SepIL.sepFormula_def.
    intros. destruct st; simpl. clear.
    split; intros.
    Focus.
    eexists; split; eauto.
      unfold SepIL.ST.HT.satisfies, SepIL.memoryIn.
      rewrite SepIL.AllWords.memoryIn_eq.
      generalize (SepIL.fcong (fun width : nat => list (word width)) 32
          (Logic.eq_sym SepIL.AllWords.allWords_eq)).
      unfold SepIL.memoryIn_def, SepIL.BedrockHeap.all_addr, mem, W, SepIL.allWords_def in *.
      generalize dependent (SepIL.AllWords.allWords 32).
      intros. generalize e. rewrite <- e; clear e.
      uip_all.
      clear. induction (pow2 32).
        compute; trivial.

        split;
          unfold SepIL.BedrockHeap.mem_get, SepIL.BedrockHeap.mem_acc, ReadByte.
          destruct (Mem $ n); split; try eexists; reflexivity.

          eassumption.

    Focus.
    unfold hpropB in *. unfold hprop in se.
    
(* TODO: This is NOT true! this probably means that i need to modify the definition of "correct" for
   the plugin... The problem is that [se] could technically require an address to not be mapped...
    destruct H. intuition.
      unfold SepIL.ST.satisfies in *.
      revert H0. revert H1.
      unfold SepIL.ST.HT.satisfies, SepIL.memoryIn.
      rewrite SepIL.AllWords.memoryIn_eq.
      generalize (SepIL.fcong (fun width : nat => list (word width)) 32
        (Logic.eq_sym SepIL.AllWords.allWords_eq)).
      unfold SepIL.hpropB, SepIL.ST.hprop in *.
      unfold mem, W, SepIL.ST.HT.smem in *.
      unfold SepIL.BedrockHeap.all_addr in *.
      revert Mem. revert x. revert se.
      generalize dependent (SepIL.AllWords.allWords 32).
      intros. revert H1. generalize dependent x.
      revert se. rewrite <- e.
      unfold SepIL.allWords_def.
      unfold SepIL.memoryIn_def. clear.
      generalize (pow2 32).
      unfold SepIL.memoryInUpto, SepIL.BedrockHeap.mem_get, SepIL.BedrockHeap.mem_acc in *.
      (** TODO: how do I prove this? **)
*)
    admit. (** TODO: NOT TRUE **)
  Qed.
*)

  Lemma symeval_read_word_correct : forall hyps pe ve s,
    symeval_read_word hyps pe s = Some ve ->
    forall cs stn uvars vars st,
      AllProvable funcs uvars vars hyps ->
      PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s)) (stn, st)) ->
      match exprD funcs uvars vars pe pcT , exprD funcs uvars vars ve pcT with
        | Some p , Some v =>
          mem_get_word _ _  footprint_w SepIL.BedrockHeap.mem_get (IL.implode stn) p (Mem st) = Some v
        | _ , _ => False
      end.
  Proof.
  Admitted.

  Theorem symeval_write_word_correct : forall hyps pe ve s s',
    symeval_write_word hyps pe ve s = Some s' ->
    forall cs stn uvars vars st v,
      AllProvable funcs uvars vars hyps ->
      exprD funcs uvars vars ve pcT = Some v ->
      PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s)) (stn, st)) ->
      match exprD funcs uvars vars pe pcT with
        | Some p =>
          match mem_set_word _ _ footprint_w SepIL.BedrockHeap.mem_set (IL.explode stn) p v (Mem st) with
            | Some m' => 
              PropX.interp cs 
                (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD s')) 
                (stn, {| Regs := Regs st ; Mem := m' |}))
            | None => False
          end
        | _ => False
      end.
  Proof.
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
  
  Local Hint Resolve pures_implied.

  Lemma stateD_pures : forall uvars vars0 specs stn s0 ss,
    stateD uvars vars0 specs stn s0 ss ->
    AllProvable funcs uvars vars0 (pures (SymMem ss)).
  Proof.
    intros. unfold stateD in *.
    destruct ss. destruct SymRegs0; destruct p; intuition;
    PropXTac.propxFo.
    sound_simp. 
    intuition; eauto.
  Qed.

  Local Hint Resolve stateD_pures.

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
    destruct ss; destruct SymRegs0; destruct p; intuition. eauto.

    sound_simp.
    unfold WriteWord. unfold BedrockHeap.mem_set in H4.
    unfold pcT, tvWord in *. rewrite H in H2. inversion H2; clear H2; subst.
    rewrite H4.
    eexists; intuition. 
  Qed.

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
        eapply symeval_read_word_correct with (vars := vars0) (uvars := uvars) 
          (cs := specs) (stn := stn) (st := s0) in H1; eauto.
        erewrite sym_loc_sound in H1 by eauto.
        unfold ReadWord, SepIL.BedrockHeap.mem_get in *.
        unfold pcT, tvWord in *.
        destruct (exprD funcs uvars vars0 rv (tvType 0)); intuition.
        eexists; intuition eauto.
        unfold stateD in *. sound_simp. intuition.

        Focus.
        sound_simp; auto.

        Focus.
        congruence.
  Qed.

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

  Theorem sym_evalInstrs_safe : forall uvars vars cs sym_instrs instrs stn st st', 
    evalInstrs stn st instrs = Some st' ->
    forall ss,
      stateD uvars vars cs stn st ss ->
      sym_instrsD uvars vars sym_instrs = Some instrs ->
      match sym_evalInstrs sym_instrs ss with
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
    clear. induction sym_instrs; simpl; intros; sound_simp; auto.
    
    case_eq (sym_evalInstr a ss); intros.    
      eapply sym_evalInstr_safe in H1; eauto.
      destruct H1. intuition. rewrite H in H5; inversion H5; clear H5; subst.
      eapply IHsym_instrs in H3; eauto.
      
      simpl. rewrite H1. rewrite H2. simpl.
      exists st. rewrite H. eauto.
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

  Lemma satisfies_hashed : forall cs uvars vars sh x hashed, 
    interp cs (![SEP.sexprD funcs sfuncs uvars vars sh] x) ->
    SEP.hash sh = (nil, hashed) ->
    interp cs (![SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD hashed)] x).
  Proof.
    clear. intros.
    generalize (SEP.hash_denote funcs sfuncs cs sh uvars vars).
    rewrite H0. simpl. intros.
    rewrite <- H1. eauto.
  Qed.

  Theorem sym_evalInstrs_apply : forall uvars vars cs instrs stn st st', 
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
    eapply sym_evalInstrs_safe; eauto.
    unfold stateD. sound_simp. intuition eauto.
    eapply satisfies_hashed; eauto.
  Qed.    

  End typed_ext.

  (* Reflect the instructions *)
  Ltac collectTypes_loc l Ts :=
    match l with
      | Reg _ => Ts
      | Imm ?i => SEP.collectTypes_expr i Ts
      | Indir _ ?i => SEP.collectTypes_expr i Ts
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

  Ltac collectTypes_lvalue l Ts :=
    match l with
      | LvReg _ => Ts
      | LvMem ?l => collectTypes_loc l Ts
    end.
  Ltac reflect_lvalue isConst l types funcs uvars vars k :=
    match l with
      | LvReg ?r => let l := constr:(@SymLvReg types r) in k funcs l 
      | LvMem ?l => 
        reflect_loc isConst l types funcs uvars vars ltac:(fun funcs l =>
          let l := constr:(@SymLvMem types l) in k funcs l)
    end.

  Ltac collectTypes_rvalue r Ts :=
    match r with
      | RvLval ?l => collectTypes_lvalue l Ts
      | RvImm ?i => SEP.collectTypes_expr i Ts
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

  Ltac collectTypes_instr i Ts :=
    match i with
      | Assign ?l ?r =>
        let Ts := collectTypes_lvalue l Ts in
        collectTypes_rvalue r Ts
      | Binop ?l ?r1 _ ?r2 =>
        let Ts := collectTypes_lvalue l Ts in
        let Ts := collectTypes_rvalue r1 Ts in
        collectTypes_rvalue r2 Ts
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

  Ltac collectTypes_instrs is Ts :=
    match is with
      | nil => Ts
      | ?i :: ?is => 
        let Ts := collectTypes_instr i Ts in
        collectTypes_instrs is Ts
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
      | Regs _ _ => true
      | _ => false
    end.

  Ltac find_reg st r :=
    match goal with
      | [ H : Regs st r = ?x |- _ ] => x
      | _ => constr:((Regs st r, @refl_equal (option W) (Some (Regs st r))))
    end.

  Existing Class PLUGIN.SymEval.

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
  
  Ltac sym_eval :=
    match goal with
      | [ H : evalInstrs ?stn ?st ?is = _ 
        , H' : PropX.interp ?cs (SepIL.SepFormula.sepFormula ?SF (?stn, ?st)) |- _ ] =>
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
            match find_reg st Sp with
              | (?sp_v, ?sp_pf) =>
                match find_reg st Rv with
                  | (?rv_v, ?rv_pf) => 
        let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
        let Ts := constr:(@nil Type) in
        let Ts := collectTypes_instrs is Ts in
        let Ts := SEP.collectAllTypes_expr isConst Ts regs in
        let Ts := SEP.collectAllTypes_sexpr isConst Ts (SF :: nil) in
        let types := eval unfold bedrock_types in bedrock_types in
        let types := SEP.extend_all_types Ts types in
        match types with
          | _ :: _ :: _ :: ?types_ext =>
            let funcs := eval unfold bedrock_funcs in (bedrock_funcs types_ext) in
            let funcs := eval simpl in funcs in
            let sfuncs := constr:(@nil (@SEP.ssignature types pcT stT)) in
            let uvars := eval simpl in (@nil _ : env types) in
            let vars := eval simpl in (@nil _ : env types) in
            reflect_instrs ltac:(isConst) is types funcs uvars vars ltac:(fun funcs sis =>
            SEP.reflect_expr ltac:(isConst) rp_v types funcs uvars vars ltac:(fun funcs rp_v =>
            SEP.reflect_expr ltac:(isConst) sp_v types funcs uvars vars ltac:(fun funcs sp_v =>
            SEP.reflect_expr ltac:(isConst) rv_v types funcs uvars vars ltac:(fun funcs rv_v =>
            SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
            match funcs with
              | _ :: _ :: _ :: ?funcs_ext =>
                build_evals sfuncs types_ext funcs_ext ltac:(fun knowns evals =>
                  idtac "using " evals ;
            generalize (@sym_evalInstrs_apply types_ext funcs_ext sfuncs knowns evals
              uvars vars cs is stn st _ H sp_v rv_v rp_v SF H'
              sp_pf rv_pf rp_pf _ (refl_equal _) sis (refl_equal _))); 
                simpl sym_evalInstrs; unfold stateD; simpl SEP.sexprD; simpl exprD; cbv iota beta; intro
            end)))))
        end
                end
            end
        end
    end.

  Goal forall cs stn st st' SF,
    PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) ->
    evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' ->
    Regs st' Rp = natToW 0.
  Proof.
    intros. sym_eval. simpl in *. intuition.
  Qed.

End BedrockEvaluator.

