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
Require Import Env.
Import List.

Require Structured SymEval.
Require Import ILEnv.

Set Implicit Arguments.
Set Strict Implicit.

(** The Symbolic Evaluation Interfaces *)
Module MEVAL := SymEval.MemoryEvaluator BedrockHeap ST.
Module SEP := MEVAL.SEP.

(** Symbolic State *)
Section SymState.
  Variable types : list type.
  Variables pcT stT : tvar.

    (** Symbolic registers **)
  Definition SymRegType : Type :=
    (expr types * expr types * expr types)%type.

    (** Symbolic State **)
  Record SymState : Type :=
    { SymVars  : variables
      ; SymUVars : variables
      ; SymMem   : option (SEP.SHeap types pcT stT)
      ; SymRegs  : SymRegType
      ; SymPures : list (expr types)
    }.

    (** Register accessor functions **)
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
End SymState.

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

  Inductive sym_assert :=
  | SymAssertCond : sym_rvalue -> test -> sym_rvalue -> option bool -> sym_assert.

  Definition istream : Type := list ((list sym_instr * option state) + sym_assert).

End typed.

Implicit Arguments sym_loc [ ].
Implicit Arguments sym_lvalue [ ].
Implicit Arguments sym_rvalue [ ].
Implicit Arguments sym_instr [ ].
Implicit Arguments sym_assert [ ].

Section Denotations.
  Variable types' : list type.
  Local Notation "'TYPES'" := (repr bedrock_types_r types').

  Local Notation "'pcT'" := (tvType 0).
  Local Notation "'tvWord'" := (tvType 0).
  Local Notation "'stT'" := (tvType 1).
  Local Notation "'tvState'" := (tvType 2).
  Local Notation "'tvTest'" := (tvType 3).
  Local Notation "'tvReg'" := (tvType 4).


  (** Denotation/reflection functions give the meaning of the reflected syntax *)
  Variable funcs' : functions TYPES.
  Local Notation "'funcs'" := (repr (bedrock_funcs_r types') funcs').
  Variable sfuncs : SEP.sfunctions TYPES pcT stT.
  Variable uvars vars : env TYPES.
  
  Definition sym_regsD (rs : SymRegType TYPES) : option regs :=
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

  Definition sym_locD (s : sym_loc TYPES) : option loc :=
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

  Definition sym_lvalueD (s : sym_lvalue TYPES) : option lvalue :=
    match s with
      | SymLvReg r => Some (LvReg r)
      | SymLvMem l => match sym_locD l with
                        | Some l => Some (LvMem l)
                        | None => None
                      end
    end.

  Definition sym_rvalueD (r : sym_rvalue TYPES) : option rvalue :=
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

  Definition sym_instrD (i : sym_instr TYPES) : option instr :=
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

  Fixpoint sym_instrsD (is : list (sym_instr TYPES)) : option (list instr) :=
    match is with
      | nil => Some nil
      | i :: is => 
        match sym_instrD i , sym_instrsD is with
          | Some i , Some is => Some (i :: is)
          | _ , _ => None
        end
    end.

  Fixpoint istreamD (is : istream TYPES) (stn : settings) (st : state) (res : option state) : Prop :=
    match is with
      | nil => Some st = res
      | inl (ins, st') :: is => 
        match sym_instrsD ins with
          | None => False
          | Some ins => 
            match st' with
              | None => evalInstrs stn st ins = None
              | Some st' => evalInstrs stn st ins = Some st' /\ istreamD is stn st' res
            end
        end
      | inr asrt :: is =>
        match asrt with
          | SymAssertCond l t r t' => 
            match sym_rvalueD l , sym_rvalueD r with
              | Some l , Some r =>
                match t' with
                  | None => 
                    Structured.evalCond l t r stn st = None
                  | Some t' =>
                    Structured.evalCond l t r stn st = Some t' /\ istreamD is stn st res
                end
              | _ , _ => False
            end
        end
    end.

  Definition stateD cs (stn_st : IL.settings * state) (ss : SymState TYPES pcT stT) : Prop :=
    let (stn,st) := stn_st in
      match ss with
        | {| SymMem := m ; SymRegs := (sp, rp, rv) ; SymPures := pures |} =>
          match 
            exprD funcs uvars vars sp tvWord ,
            exprD funcs uvars vars rp tvWord ,
            exprD funcs uvars vars rv tvWord
            with
            | Some sp , Some rp , Some rv =>
              Regs st Sp = sp /\ Regs st Rp = rp /\ Regs st Rv = rv
            | _ , _ , _ => False
          end
          /\ match m with 
               | None => True
               | Some m => 
                 PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD m)) stn_st)%PropX
             end
          /\ AllProvable funcs uvars vars pures 
      end.

  Section SymEvaluation.
    Variable Prover : ProverT TYPES.
    Variable meval : MEVAL.MemEvaluator TYPES pcT stT.

    Section with_facts.
    Variable Facts : Facts Prover.

    Definition sym_evalLoc (lv : sym_loc TYPES) (ss : SymState TYPES pcT stT) : expr TYPES :=
      match lv with
        | SymReg r => sym_getReg r (SymRegs ss)
        | SymImm l => l
        | SymIndir r w => fPlus (sym_getReg r (SymRegs ss)) w
      end.

    Definition sym_evalLval (lv : sym_lvalue TYPES) (val : expr TYPES) (ss : SymState TYPES pcT stT)
      : option (SymState TYPES pcT stT) :=
      match lv with
        | SymLvReg r =>
          Some {| SymVars := SymVars ss
            ; SymUVars := SymUVars ss
            ; SymMem := SymMem ss 
            ; SymRegs := sym_setReg r val (SymRegs ss)
            ; SymPures := SymPures ss
          |}
        | SymLvMem l => 
          let l := sym_evalLoc l ss in
            match SymMem ss with
              | None => None
              | Some m =>
                match MEVAL.smemeval_write_word meval _ Facts l val m with
                  | Some m =>
                    Some {| SymVars := SymVars ss
                      ; SymUVars := SymUVars ss
                      ; SymMem := Some m
                      ; SymRegs := SymRegs ss
                      ; SymPures := SymPures ss
                    |}
                  | None => None
                end
            end
      end.

    Definition sym_evalRval (rv : sym_rvalue TYPES) (ss : SymState TYPES pcT stT) : option (expr TYPES) :=
      match rv with
        | SymRvLval (SymLvReg r) =>
          Some (sym_getReg r (SymRegs ss))
        | SymRvLval (SymLvMem l) =>
          let l := sym_evalLoc l ss in
            match SymMem ss with
              | None => None
              | Some m => 
                MEVAL.smemeval_read_word meval _ Facts l m
            end
        | SymRvImm w => Some w 
        | SymRvLabel l => None (* TODO: can we use labels? it seems like we need to reflect these as words. *)
        (* an alternative would be to reflect these as a function call that does the positioning...
         * - it isn't clear that this can be done since the environment would need to depend on the settings.
         *)
        (*Some (Expr.Const (TYPES := TYPES) (t := tvType 2) l) *)
      end.

    Definition sym_assertTest (r : sym_rvalue TYPES) (t : test) (l : sym_rvalue TYPES) (ss : SymState TYPES pcT stT) (res : bool) 
      : option (expr TYPES) :=
      let '(l, t, r) := 
        if res then (l, t, r)
          else match t with
                 | IL.Eq => (l, IL.Ne, r)
                 | IL.Ne => (l, IL.Eq, r)
                 | IL.Lt => (r, IL.Le, l)
                 | IL.Le => (r, IL.Lt, l)
               end
          in
          match sym_evalRval l ss , sym_evalRval r ss with
            | Some l , Some r =>
              match t with
                | IL.Eq => Some (Expr.Equal tvWord l r)
                | _ => Some (Expr.Func 3 (Expr.Const (types := TYPES) (t := tvTest) t :: l :: r :: nil))
              end
            | _ , _ => None
          end.

    Definition sym_evalInstr (i : sym_instr TYPES) (ss : SymState TYPES pcT stT) : option (SymState TYPES pcT stT) :=
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
                end _ l r
                in
                sym_evalLval lv v ss
            | _ , _ => None
          end
      end.

    Fixpoint sym_evalInstrs (is : list (sym_instr TYPES)) (ss : SymState TYPES pcT stT) 
      : SymState TYPES pcT stT + (SymState TYPES pcT stT * list (sym_instr TYPES)) :=
      match is with
        | nil => inl ss
        | i :: is =>
          match sym_evalInstr i ss with
            | None => inr (ss, i :: is)
            | Some ss => sym_evalInstrs is ss
          end
      end.
    End with_facts.
    
    Variable learnHook : MEVAL.LearnHook TYPES (SymState TYPES pcT stT).

    Fixpoint sym_evalStream (facts : Facts Prover) (is : istream TYPES) (ss : SymState TYPES pcT stT) 
      : option (SymState TYPES pcT stT) + (SymState TYPES pcT stT * istream TYPES) :=
      match is with
        | nil => inl (Some ss)
        | inl (ins, st) :: is =>
          match sym_evalInstrs facts ins ss with
            | inr (ss,rm) => inr (ss, inl (rm, st) :: is)
            | inl ss => sym_evalStream facts is ss
          end
        | inr asrt :: is =>
          match asrt with
            | SymAssertCond l t r (Some res) =>
              match sym_assertTest facts l t r ss res with
                | Some sp =>
                  let facts' := Learn Prover facts (sp :: nil) in 
                  let ss' := 
                    {| SymVars := SymVars ss
                     ; SymUVars := SymUVars ss
                     ; SymRegs := SymRegs ss 
                     ; SymMem := SymMem ss
                     ; SymPures := sp :: SymPures ss
                     |}
                  in
                  let ss' := learnHook Prover ss' facts' in
                  sym_evalStream facts' is ss'
                | None => inr (ss, inr asrt :: is)
              end
            | SymAssertCond l t r None =>
              match sym_evalRval facts l ss , sym_evalRval facts r ss with
                | None , _ => inl None
                | _ , None => inl None
                | _ , _ => sym_evalStream facts is ss 
              end
          end
      end.
    
    Section Correctness.
      Definition IL_stn_st : Type := (IL.settings * IL.state)%type.

      Definition IL_mem_satisfies (cs : PropX.codeSpec (tvarD TYPES pcT) (tvarD TYPES stT)) 
        (P : ST.hprop (tvarD TYPES pcT) (tvarD TYPES stT) nil) (stn_st : IL_stn_st) : Prop :=
        PropX.interp cs (SepIL.SepFormula.sepFormula P stn_st).
      
      Definition IL_ReadWord : IL_stn_st -> tvarD TYPES tvWord -> option (tvarD TYPES tvWord) :=
        (fun stn_st => IL.ReadWord (fst stn_st) (Mem (snd stn_st))).
      Definition IL_WriteWord : IL_stn_st -> tvarD TYPES tvWord -> tvarD TYPES tvWord -> option IL_stn_st :=
        (fun stn_st p v => 
          let (stn,st) := stn_st in
            match IL.WriteWord stn (Mem st) p v with
              | None => None
              | Some m => Some (stn, {| Regs := Regs st ; Mem := m |})
            end).

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

      Lemma sym_evalLoc_correct : forall loc ss res res' stn_st locD cs,
        stateD cs stn_st ss ->
        sym_locD loc = Some locD ->
        evalLoc (snd stn_st) locD = res' ->
        sym_evalLoc loc ss = res -> 
        exprD funcs uvars vars res tvWord = Some res'.
      Proof.
        destruct loc; unfold stateD; destruct ss; destruct SymRegs0; destruct p; t_correct.
      Qed.

      Variable PC : ProverT_correct Prover funcs.
      Variable meval_correct : MEVAL.MemEvaluator_correct meval funcs sfuncs tvWord tvWord 
        IL_mem_satisfies IL_ReadWord IL_WriteWord.

      Section with_facts.
        Variable facts : Facts Prover.
        Hypothesis Valid_facts : Valid PC uvars vars facts.

        Lemma sym_evalRval_correct : forall rv ss res stn_st rvD cs,
          stateD cs stn_st ss ->
          sym_rvalueD rv = Some rvD ->
          sym_evalRval facts rv ss = Some res ->
          exists val,
            evalRvalue (fst stn_st) (snd stn_st) rvD = Some val /\
            exprD funcs uvars vars res tvWord = Some val.
        Proof.
          destruct rv; unfold stateD; t_correct; try congruence;
            try solve [
              destruct ss; destruct SymRegs0; destruct p; intuition; t_correct; eauto ].

            destruct s; t_correct; destruct ss; destruct SymRegs0; destruct p; intuition; t_correct; eauto.
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
          stateD cs stn_st ss ->
          sym_lvalueD lv = Some lvD ->
          sym_evalLval facts lv val ss = Some ss' ->
          exprD funcs uvars vars val tvWord = Some valD ->
          exists st', 
            evalLvalue (fst stn_st) (snd stn_st) lvD valD = Some st' /\
            stateD cs (fst stn_st, st') ss'.
        Proof.
          destruct lv.
            destruct ss; destruct SymRegs0; destruct p;
            t_correct; eexists; repeat (split; try reflexivity; eauto);
            try solve [ repeat rewrite sepFormula_eq in *; unfold sepFormula_def in *; simpl in *; auto ].

            t_correct.
            eapply sym_evalLoc_correct with (stn_st := (s0, s1)) in H0; simpl in *; eauto.
            match goal with
              | [ H : MEVAL.smemeval_write_word _ _ _ _ _ _ = _ |- _ ] => 
                eapply (MEVAL.WriteCorrect meval_correct) with (cs := cs) (stn_m := (s0,s1)) in H; eauto
            end.
            Focus 2. destruct ss; simpl in *; t_correct. destruct SymRegs0; destruct p; intuition.

            destruct (WriteWord s0 (Mem s1) (evalLoc s1 l) valD); intuition; try contradiction.
            eexists; split ; [ reflexivity | ].
            destruct ss; destruct SymRegs0; destruct p; simpl in *. intuition eauto.
        Qed.

        Lemma sym_evalInstr_correct : forall instr stn_st instrD cs ss ss',
          stateD cs stn_st ss ->
          sym_instrD instr = Some instrD ->
          sym_evalInstr facts instr ss = Some ss' ->
          exists st',
            evalInstr (fst stn_st) (snd stn_st) instrD = Some st' /\
            stateD cs (fst stn_st, st') ss'.
        Proof.
          Opaque stateD.
          destruct instr; t_correct; simpl.
          eapply sym_evalRval_correct in H1; eauto; simpl in *.
          destruct H1. intuition.
          eapply sym_evalLval_correct in H2; eauto; simpl in *.
          destruct H2. intuition. t_correct; eauto.

          repeat match goal with
                   | [ H : exists x, _ |- _ ] => destruct H
                   | [ H : _ /\ _ |- _ ] => destruct H
                   | [ H : sym_rvalueD _ = _ |- _ ] =>
                     eapply sym_evalRval_correct in H; eauto
                 end.
          
          destruct b; eapply sym_evalLval_correct in H3; eauto; t_correct; eauto.
        Qed.

        Lemma sym_evalInstrs_correct : forall is stn_st isD cs ss,
          stateD cs stn_st ss ->
          sym_instrsD is = Some isD ->
          match evalInstrs (fst stn_st) (snd stn_st) isD with
            | Some st' => 
              match sym_evalInstrs facts is ss with
                | inl ss' => stateD cs (fst stn_st, st') ss'
                | inr (ss', is') => 
                  match sym_instrsD is' with
                    | None => False
                    | Some is'D => 
                      exists st'', stateD cs (fst stn_st, st'') ss' /\
                        evalInstrs (fst stn_st) st'' is'D = Some st'
                  end
              end
            | None => 
              match sym_evalInstrs facts is ss with
                | inl ss' => False
                | inr (ss', is') => 
                  match sym_instrsD is' with
                    | None => False
                    | Some is'D => 
                      exists st'', stateD cs (fst stn_st, st'') ss' /\
                        evalInstrs (fst stn_st) st'' is'D = None
                  end
              end
          end.
        Proof.
          induction is; simpl; intros;
            repeat match goal with
                     | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                   end; simpl.
          destruct stn_st; simpl in *; eauto.

          Opaque stateD.
          t_correct.
          simpl in *.
          case_eq (evalInstr s s0 i); intros.
          Focus 2.
          case_eq (sym_evalInstr facts a ss); intros.
          exfalso. eapply sym_evalInstr_correct in H3; eauto.
          destruct H3; simpl in *; intuition congruence.
          simpl; t_correct.
          exists s0. simpl. rewrite H2. intuition.

          case_eq (sym_evalInstr facts a ss); intros.
          eapply sym_evalInstr_correct in H3; eauto. simpl in *.
          destruct H3. intuition. clear H.
          
          rewrite H2 in H4; inversion H4; clear H4; subst.

          eapply IHis in H1; eauto; simpl in *; eauto.


          simpl; t_correct. case_eq (evalInstrs s s1 l); intros.
          eexists s0. t_correct; intuition.
          eexists s0. t_correct; intuition.
          Transparent stateD.
        Qed.

        Lemma sym_assertTest_correct : forall cs r rD t l lD ss stn_st,
          stateD cs stn_st ss ->
          sym_rvalueD r = Some rD ->
          sym_rvalueD l = Some lD ->
          forall res, 
          match Structured.evalCond rD t lD (fst stn_st) (snd stn_st) with
            | None =>
              match sym_assertTest facts r t l ss res with
                | Some _ => False
                | None => True
              end
            | Some res' =>
              match sym_assertTest facts r t l ss res with
                | Some b => 
                  Provable funcs uvars vars b
                | None => True
              end
          end.
        Proof.
          destruct res.
          unfold sym_assertTest; intros;
            repeat match goal with
                     | [ |- context [ sym_evalRval ?F ?X ?Y ] ] =>
                       case_eq (sym_evalRval F X Y); intros
                     | [ |- match ?X with 
                              | None => True
                              | Some _ => True
                            end ] => destruct X; trivial
                   end.
(*
          | 
          intros. 
           match goal with
                           | [ H : exists x, _ |- _ ] => destruct H
                           | [ H : _ /\ _ |- _ ] => destruct H
                           | [ H : sym_rvalueD _ = _ |- _ ] =>
                             eapply sym_evalRval_correct in H; eauto
                         end.
                         *)
        Admitted.
      End with_facts.
    End Correctness.
  End SymEvaluation.
End Denotations.


(** Unfortunately, most things can change while evaluating a stream,
 ** so we have to move it outside the sections
 **)
Section stream_correctness.
  Variable types' : list type.
  Local Notation "'TYPES'" := (repr bedrock_types_r types').

  Local Notation "'pcT'" := (tvType 0).
  Local Notation "'tvWord'" := (tvType 0).
  Local Notation "'stT'" := (tvType 1).
  Local Notation "'tvState'" := (tvType 2).
  Local Notation "'tvTest'" := (tvType 3).
  Local Notation "'tvReg'" := (tvType 4).

  Variable funcs' : functions TYPES.
  Local Notation "'funcs'" := (repr (bedrock_funcs_r types') funcs').
  Variable sfuncs : SEP.sfunctions TYPES pcT stT.

  Variable meval : MEVAL.MemEvaluator TYPES pcT stT.
  Variable meval_correct : MEVAL.MemEvaluator_correct meval funcs sfuncs tvWord tvWord 
    (@IL_mem_satisfies types') (@IL_ReadWord types') (@IL_WriteWord types').

  Variable Prover : ProverT TYPES.
  Variable PC : ProverT_correct Prover funcs.

  Variable learnHook : MEVAL.LearnHook TYPES (SymState TYPES pcT stT).
  Variable learn_correct : @MEVAL.LearnHook_correct _ pcT stT _ learnHook (@stateD _ funcs sfuncs) funcs sfuncs.

(*
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


  Lemma sym_evalStream_correct : forall sound_or_safe path stn uvars vars st,
    istreamD funcs uvars vars path stn st sound_or_safe ->
    forall cs ss,
      stateD funcs sfuncs uvars vars cs (stn,st) ss ->
      forall facts, 
        Valid PC uvars vars facts ->
        let res := sym_evalStream Prover meval learnHook facts path ss in
          match sound_or_safe with
            | None =>
                  (** safe **)
              match res with
                | inl None => True
                | inl (Some _) => False
                | inr (ss'', is') => 
                  exists st'' : state, 
                    SEP.forallEach (SymVars ss'') (fun vars =>
                      SEP.existsEach 
                    istreamD funcs (SymUVars ss'') vars is' stn st'' None
                    /\ stateD funcs sfuncs uvars vars cs (stn, st'') ss''
              end
            | Some st' =>
                  (** correct **)
              match res with
                | inl None => False                
                | inl (Some ss') => stateD funcs sfuncs uvars vars cs (stn, st') ss'
                | inr (ss'', is') => 
                  exists st'' : state, 
                    istreamD funcs uvars vars is' stn st'' (Some st')
                    /\ stateD funcs sfuncs uvars vars cs (stn, st'') ss''
              end
          end.
  Proof.
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
      Admitted.
*)

  Lemma sym_eval_any :     
    forall uvars vars sound_or_safe path stn st,
      istreamD funcs uvars vars path stn st sound_or_safe ->
      forall cs ss,
      stateD funcs sfuncs uvars vars cs (stn,st) ss ->
      forall facts, 
        Valid PC uvars vars facts ->
      let res := @sym_evalStream _ Prover meval learnHook facts path ss in
      match sound_or_safe with
        | None =>
            (** safe **)
            match res with
              | inl None => True
              | inl (Some _) => False
              | inr (ss'', is') => 
                exists st'' : state, 
                  istreamD funcs uvars vars is' stn st'' None
                  /\ stateD funcs sfuncs uvars vars cs (stn, st'') ss''
            end
          | Some st' =>
            (** correct **)
            match res with
              | inl None => False                
              | inl (Some ss') => stateD funcs sfuncs uvars vars cs (stn, st') ss'
              | inr (ss'', is') => 
                exists st'' : state, 
                  istreamD funcs uvars vars is' stn st'' (Some st')
                  /\ stateD funcs sfuncs uvars vars cs (stn, st'') ss''
            end
        end.
  Proof.
    revert learn_correct; revert PC; revert meval_correct. (* NOTE: I have to do this to prevent coq from removing them *)
      admit.
(*
      induction path; simpl; intros;
        repeat (congruence || 
          match goal with
            | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
            | [ H : prod _ _ |- _ ] => destruct H
            | [ H : SymRegType _ |- _ ] => destruct H
            | [ H : match ?S with
                      | {| SymMem := _ |} => _
                    end |- _ ] => destruct S

            | [ H : match ?X with
                      | inl _ => _
                      | inr _ => _
                    end |- _ ] => revert H; case_eq X; intros; subst
            | [ H : match ?X with
                      | Some _ => _
                      | None => _
                    end |- _ ] => revert H; case_eq X; intros; subst
          end || intuition).
      
      revert PC; revert learn_correct.
      Focus 9.
*)
  Qed.

  Theorem Apply_sym_eval : forall stn uvars vars sound_or_safe st path,
    istreamD funcs uvars vars path stn st sound_or_safe ->
    forall cs ss,
      stateD funcs sfuncs uvars vars cs (stn,st) ss ->
      let facts := Summarize Prover (match SymMem ss with
                                       | None => SymPures ss
                                       | Some m => pures m ++ SymPures ss
                                     end) in
      let res := @sym_evalStream _ Prover meval learnHook facts path ss in
      match sound_or_safe with
        | None =>
            (** safe **)
            match res with
              | inl None => True
              | inl (Some _) => False
              | inr (ss'', is') => 
                exists st'' : state, 
                  istreamD funcs uvars vars is' stn st'' None
                  /\ stateD funcs sfuncs uvars vars cs (stn, st'') ss''
            end
          | Some st' =>
            (** correct **)
            match res with
              | inl None => False                
              | inl (Some ss') => stateD funcs sfuncs uvars vars cs (stn, st') ss'
              | inr (ss'', is') => 
                exists st'' : state, 
                  istreamD funcs uvars vars is' stn st'' (Some st')
                  /\ stateD funcs sfuncs uvars vars cs (stn, st'') ss''
            end
        end.
  Proof.
    intros; eapply sym_eval_any; eauto.
    unfold facts. destruct PC. simpl. eapply Summarize_correct.
    revert H0; clear.
    destruct ss; destruct SymRegs0; destruct p; simpl; clear; intuition.
    destruct SymMem0; auto.
    eapply AllProvable_app; eauto.
    
    generalize SEP.sheapD_pures. unfold ST.satisfies.
    intro XX.
    rewrite sepFormula_eq in H0. unfold sepFormula_def in *.
    simpl in *.
    specialize (XX _ (repr (bedrock_funcs_r types') funcs) (tvType 0) (tvType 1)); eauto. 
  Qed.

  Lemma goto_proof : forall (specs : codeSpec W (settings * state)) CPTR CPTR' x4,
    specs CPTR = Some (fun x : settings * state => x4 x) ->
    CPTR = CPTR' ->
    forall (stn_st : settings * state) Z,
      interp specs (Z ---> x4 stn_st) ->
      interp specs Z ->
      exists pre' : spec W (settings * state),
        specs CPTR' = Some pre' /\ interp specs (pre' stn_st).
  Proof.
    clear; intros; subst.
    eexists. split. eassumption. eapply Imply_E. eapply H1. auto.
  Qed.

  Theorem stateD_proof_no_heap :
    forall (uvars vars : Expr.env TYPES) (st : state) (sp rv rp : Expr.expr TYPES),
      exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
      exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
      exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
      forall pures : list (Expr.expr TYPES),
        Expr.AllProvable funcs uvars vars pures ->
        forall (cs : codeSpec W (settings * state)) (stn : settings),
          stateD funcs' sfuncs uvars vars cs (stn, st)
          {| SymVars := map (@projT1 _ _) vars
            ; SymUVars := map (@projT1 _ _) uvars
            ; SymMem := None
            ; SymRegs := (sp, rp, rv)
            ; SymPures := pures
          |}.
  Proof.
    unfold stateD. intros.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end.
    intuition auto.
  Qed.

  Theorem stateD_proof :
    forall (uvars vars : Expr.env TYPES) (st : state) (sp rv rp : Expr.expr TYPES),
      exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
      exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
      exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
      forall pures : list (Expr.expr TYPES),
        Expr.AllProvable funcs uvars vars pures ->
        forall (sh : SEP.sexpr TYPES pcT stT)
          (hashed : SEP.SHeap TYPES pcT stT),
          SEP.hash sh = (nil, hashed) ->
          forall (cs : codeSpec W (settings * state)) (stn : settings),
            interp cs (![SEP.sexprD funcs sfuncs uvars vars sh] (stn, st)) ->
            stateD funcs' sfuncs uvars vars cs (stn, st)
            {| SymVars := map (@projT1 _ _) vars
              ; SymUVars := map (@projT1 _ _) uvars
              ; SymMem := Some hashed
              ; SymRegs := (sp, rp, rv)
              ; SymPures := pures
            |}.
  Proof.
    unfold stateD. intros.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end.
    intuition auto.
    generalize (SEP.hash_denote funcs sfuncs cs sh). rewrite H3. simpl in *.
    intro XX. rewrite <- XX. eauto.
  Qed.
End stream_correctness.

(** Reflection **)

(* Reflect the instructions *)
Ltac collectTypes_loc isConst l Ts :=
  match l with
    | Reg _ => Ts
    | Imm ?i => collectTypes_expr isConst i Ts
    | Indir _ ?i => collectTypes_expr isConst i Ts
  end.
Ltac reify_loc isConst l types funcs uvars vars k :=
  match l with
    | Reg ?r => 
      let res := constr:(@SymReg types r) in
        k uvars funcs res
    | Imm ?i =>
      reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        let l := constr:(@SymImm types i) in k uvars funcs l)
    | Indir ?r ?i =>
      reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        let l := constr:(@SymIndir types r i) in k uvars funcs l)
  end.

Ltac collectTypes_lvalue isConst l Ts :=
  match l with
    | LvReg _ => Ts
    | LvMem ?l => collectTypes_loc isConst l Ts
  end.
Ltac reify_lvalue isConst l types funcs uvars vars k :=
  match l with
    | LvReg ?r => let l := constr:(@SymLvReg types r) in k uvars funcs l 
    | LvMem ?l => 
      reify_loc isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        let l := constr:(@SymLvMem types l) in k uvars funcs l)
  end.

Ltac collectTypes_rvalue isConst r Ts :=
  match r with
    | RvLval ?l => collectTypes_lvalue isConst l Ts
    | RvImm ?i => collectTypes_expr isConst i Ts
    | RvLabel _ => let l := constr:(label:Type) in Reflect.cons_uniq l Ts
  end.

Ltac reify_rvalue isConst r types funcs uvars vars k :=
  match r with
    | RvLval ?l =>
      reify_lvalue isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        let l := constr:(@SymRvLval types l) in k uvars funcs l)
    | RvImm ?i =>
      reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        let l := constr:(@SymRvImm types i) in k uvars funcs l)
    | RvLabel ?l => 
      let r := constr:(@SymRvLabel types l) in k uvars funcs r
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
Ltac reify_instr isConst i types funcs uvars vars k :=
  match i with
    | Assign ?l ?r =>
      reify_lvalue isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        reify_rvalue isConst r types funcs uvars vars ltac:(fun uvars funcs r =>
          let res := constr:(@SymAssign types l r) in k uvars funcs res))
    | Binop ?l ?r1 ?o ?r2 =>
      reify_lvalue isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        reify_rvalue isConst r1 types funcs uvars vars ltac:(fun uvars funcs r1 =>
          reify_rvalue isConst r2 types funcs uvars vars ltac:(fun uvars funcs r2 =>
            let res := constr:(@SymBinop types l r1 o r2) in k uvars funcs res)))
  end.

Ltac collectTypes_instrs isConst is Ts :=
  match is with
    | nil => Ts
    | ?i :: ?is => 
      let Ts := collectTypes_instr isConst i Ts in
        collectTypes_instrs isConst is Ts
  end.
Ltac reify_instrs isConst is types funcs uvars vars k :=
  match is with
    | nil => 
      let is := constr:(@nil (sym_instr types)) in k uvars funcs is
    | ?i :: ?is =>
      reify_instr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        reify_instrs isConst is types funcs uvars vars ltac:(fun uvars funcs is =>
          let res := constr:(i :: is) in k uvars funcs res))
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

Ltac open_stateD H0 :=
  cbv beta iota zeta delta 
    [ stateD Expr.exprD Expr.applyD
      EquivDec.equiv_dec 
      Expr.Range Expr.Domain Expr.Denotation
      Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
      sumbool_rec sumbool_rect
      Peano_dec.eq_nat_dec nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym
      nth_error map value
      f_equal

      Expr.AllProvable Expr.Provable Expr.tvarD comparator
    ] in H0; 
    let a := fresh in 
    let b := fresh in
    let zz := fresh in destruct H0 as [ a [ b zz ] ] ;
    destruct a as [ ? [ ? ? ] ];
    repeat match type of zz with
             | True => clear zz
             | _ /\ _ => let v := fresh in destruct zz as [ v zz ]
           end.

Ltac get_instrs st :=
  let rec find_exact H Hs :=
    match Hs with
      | tt => false
      | H :: _ => true
      | _ :: ?Hs => find_exact H Hs
    end
    in
    let rec get_instrs st ignore :=
      match goal with
        | [ H : Structured.evalCond ?l _ ?r _ st = Some _ |- _ ] =>
          match find_exact H ignore with
            | false =>
              let v := get_instrs st (H, ignore) in
                constr:((((l,r), H), v))
          end
        | [ H : Structured.evalCond ?l _ ?r _ st = None |- _ ] =>
          constr:((((l,r), H), tt))
        | [ H : evalInstrs _ st ?is = Some ?X |- _ ] =>
          let v := get_instrs X tt in
            constr:(((is, H), v))
        | [ H : evalInstrs _ st ?is = None |- _ ] =>
          constr:(((is, H), tt))
        | [ |- _ ] => tt
      end
      in get_instrs st tt.
Ltac collectAllTypes_instrs is Ts :=
  match is with
    | tt => Ts
    | (((?l,?r), _), ?is) =>
      let Ts := collectTypes_rvalue ltac:(isConst) l Ts in
        let Ts := collectTypes_rvalue ltac:(isConst) r Ts in
          collectAllTypes_instrs is Ts
    | ((?i, _), ?is) =>
      let Ts := collectTypes_instrs ltac:(isConst) i Ts in
        collectAllTypes_instrs is Ts
  end.

Ltac build_path types instrs st uvars vars funcs k :=
  match instrs with
    | tt => 
      let is := constr:(nil : @istream types) in
      let pf := constr:(refl_equal (Some st)) in
      k uvars funcs is (Some st) pf
    | ((?i, ?H), ?is) =>
      match type of H with
        | Structured.evalCond ?l ?t ?r _ ?st = ?st' =>
          reify_rvalue ltac:(isConst) l types funcs uvars vars ltac:(fun uvars funcs l =>
            reify_rvalue ltac:(isConst) r types funcs uvars vars ltac:(fun uvars funcs r =>
              match st' with
                | None => 
                  let i := constr:(inr (@SymAssertCond types l t r st') :: (nil : @istream types)) in
                  k uvars funcs i (@None state) H
                | Some ?st'' => 
                  build_path types is st uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                    let i := constr:(inr (@SymAssertCond types l t r st') :: is) in
                    let pf := constr:(@conj _ _ H pf) in
                    k uvars funcs i sf pf)
              end))
        | evalInstrs _ ?st _ = ?st' =>
          reify_instrs ltac:(isConst) i types funcs uvars vars ltac:(fun uvars funcs sis =>
            match st' with
              | None => 
                let i := constr:(inl (sis, None) :: (nil : @istream types)) in
                  k uvars funcs i (@None state) H
              | Some ?st'' =>
                build_path types is st'' uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                  let i := constr:(inl (sis, st') :: is) in
                  let pf := constr:(@conj _ _ H pf) in
                  k uvars funcs i sf pf)
            end)
      end
  end.

Goal forall (cs : codeSpec W (settings * state)) (stn : settings) st st',
  Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
  evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' -> 
  True.
  intros.
  match goal with
    | [ |- _ ] => 
      let i := get_instrs st in
      let Ts := constr:(@nil Type) in
      let Ts := collectAllTypes_instrs i Ts in
      let types_ := eval unfold bedrock_types in bedrock_types in
      let types_ := Expr.extend_all_types Ts types_ in
      let typesV := fresh "types" in
      pose (typesV := types_) ;
      let v := constr:(nil : env typesV) in
      let f := eval unfold ILEnv.bedrock_funcs in (ILEnv.bedrock_funcs typesV) in
      build_path typesV i st v v f ltac:(fun uvars funcs is sf pf =>
        assert (@istreamD typesV funcs uvars v is stn st sf)  by (exact pf))
  end.
  solve [ trivial ].
Abort.

(** NOTE:
 ** - [isConst] is an ltac function of type [* -> bool]
 ** - [prover] is an ltac with "type" (assuming [PR] is the prover to use)
 **     [forall ts (fs : functions ts), ProverT_correct ts PR fs]. 
 ** - [plugin] is an ltac with "type" (assuming [PL] is the plugin to use)
 **     [forall ts pcT stT (fs : functions ts) (ps : sfunctions ts pcT stT), SymEvaluator_correct ts fs ps PL]
 ** - [unfolder] is an ltac with "type" (assuming [U] is the unfolder to use)
 **     [forall ts pcT stT (fs : functions ts) (ps : sfunctions ts pcT stT), LearnHook_correct ts (Facts PR) U fs ps]
 ** - [simplifier] is an ltac that takes a hypothesis names and simplifies it
 **     (this should be implmented using [cbv beta iota zeta delta [ ... ] in H])
 **     (it is recommended/necessary to call [sym_evaluator] or import its simplification)
 ** - [Ts] is the list of seed types, [list type]
 ** - [Fs] is an ltac that produces the list of seed functions, [tuple-of (_ -> ... -> _)]
 **     (values that are [tt] may be overridden)
 ** - [SFs] is an ltac that produces the list of seed predicates, [tuple-of (_ -> ... -> _ -> hprop _)]
 **     (values that are [tt] may be overriden)
 **)
Ltac sym_eval isConst prover plugin unfolder simplifier Ts Fs SFs :=
  let rec init_from st :=
    match goal with
      | [ H : evalInstrs _ ?st' _ = Some st |- _ ] => init_from st'
      | [ |- _ ] => st
    end
  in          
  let shouldReflect P :=
    match P with
      | evalInstrs _ _ _ = _ => false
      | Structured.evalCond _ _ _ _ _ = _ => false
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
      | _ => match type of Ts with
               | list Type => Ts
               | ?TTs => fail 10 "Ts must have type (list Type), got " TTs
             end
    end
  in
  match Fs with 
    | tt => idtac
    | (_ , _) => idtac 
    | _ => fail 10 "Fs must be a tuple of functions, got " Fs
  end ;
  match SFs with 
    | tt => idtac
    | (_ , _) => idtac 
    | _ => fail 10 "SFs must be a tuple of predicates, got " Fs
  end ;
  let stn_st_SF :=
    match goal with
      | [ H : interp _ (![ ?SF ] ?X) |- _ ] => constr:((X, (SF, H)))
      | [ H : Structured.evalCond _ _ _ ?stn ?st = _ |- _ ] => 
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ H : IL.evalInstrs ?stn ?st _ = _ |- _ ] =>
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ |- _ ] => tt
    end
  in
  let cs :=
    match goal with
      | [ H : codeSpec _ _ |- _ ] => H
    end
  in
  match stn_st_SF with
    | tt => idtac (* nothing to symbolically evluate *)
    | ((?stn, ?st), ?SF) =>
      match find_reg st Rp with
        | (?rp_v, ?rp_pf) =>
          match find_reg st Sp with
            | (?sp_v, ?sp_pf) =>
              match find_reg st Rv with
                | (?rv_v, ?rv_pf) =>
                  let all_instrs := get_instrs st in
                  let all_props := Expr.collect_props shouldReflect in
                  let pures := Expr.props_types all_props in

                  let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
                  (** collect the raw types **)
                  let Ts := collectAllTypes_instrs all_instrs Ts in
                  let Ts := Expr.collectTypes_exprs ltac:(isConst) regs Ts in
                  let Ts := Expr.collectTypes_exprs ltac:(isConst) pures Ts in
                  let Ts := 
                    match SF with
                      | tt => Ts 
                      | (?SF, _) => SEP.collectAllTypes_sexpr isConst Ts (SF :: nil)
                    end
                  in
                  let Ts := Expr.collectAllTypes_funcs Ts Fs in
                  let Ts := SEP.collectAllTypes_sfuncs Ts SFs in
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
                  let types_ := eval unfold bedrock_types in bedrock_types in
                  let types_ := Expr.extend_all_types Ts types_ in
                  let typesV := fresh "types" in
                  pose (typesV := types_);
                  (** **)
                  let pcT := constr:(tvType 0) in
                  let stT := constr:(tvType 1) in
                  (** build the variables **)
                  let uvars := eval simpl in (@nil _ : Expr.env typesV) in
                  let vars := uvars in
                  (** build the base functions **)
                  let funcs := eval unfold bedrock_funcs in (@bedrock_funcs typesV) in
                  let funcs := Expr.getAllFunctions typesV funcs Fs in
                  let funcs := eval simpl in funcs in
                  (** build the base sfunctions **)
                  let sfuncs := constr:(@nil (@SEP.ssignature typesV pcT stT)) in
                  let sfuncs := SEP.getAllSFunctions pcT stT typesV sfuncs SFs in
                  (** reflect the expressions **)
                  Expr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
                  let proofs := Expr.props_proof all_props in
                  Expr.reify_expr ltac:(isConst) rp_v typesV funcs uvars vars ltac:(fun uvars funcs rp_v =>
                  Expr.reify_expr ltac:(isConst) sp_v typesV funcs uvars vars ltac:(fun uvars funcs sp_v =>
                  Expr.reify_expr ltac:(isConst) rv_v typesV funcs uvars vars ltac:(fun uvars funcs rv_v =>
                    let finish H syms :=
                      let rec unfold_all syms :=
                        match syms with
                          | tt => idtac
                          | (?X, ?Y) => unfold_all X ; unfold_all Y
                          | ?X => subst X
                        end
                      in
                      unfold_all syms ; 
                      first [ simplifier H | fail 100000 "simplifier failed!" ] ;
                      (try assumption || destruct H as [ [ ? [ ? ? ] ] [ ? ? ] ])
                    in
                    build_path typesV all_instrs st uvars vars funcs ltac:(fun uvars funcs is fin_state is_pf =>
                      match SF with
                        | tt =>
                          let funcsV := fresh "funcs" in
                          pose (funcsV := funcs) ;
                          let sfuncsV := fresh "sfuncs" in
                          pose (sfuncsV := sfuncs) ;
                          let proverCV := fresh "proverC" in
                          let proverC := prover typesV funcsV in
                          pose (proverCV := proverC) ;
                          plugin typesV pcT stT funcsV sfuncsV ltac:(fun plugin_syms pluginC =>
                          let pluginCV := fresh "plugin" in
                          pose (pluginCV := pluginC) ;
                          let unfolderC := unfolder typesV pcT stT funcsV sfuncsV in
                          let unfolderCV := fresh "unfolder" in
                          pose (unfolderCV := unfolderC) ;
                          generalize (@stateD_proof_no_heap typesV funcsV sfuncsV
                            uvars vars st sp_v rv_v rp_v 
                            sp_pf rv_pf rp_pf pures proofs cs stn) ;
                          let H_stateD := fresh in
                          intro H_stateD ;
                          (apply (@Apply_sym_eval typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                              stn uvars vars fin_state st is is_pf) in H_stateD ;
                           let syms := constr:((typesV, (funcsV, (sfuncsV, (proverCV, (pluginCV, unfolderCV)))))) in
                           finish H_stateD syms) || fail 100000 "couldn't apply sym_eval_any! (non-SF case)"
(*
                             first [
                               generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV stn uvars vars _ _ _ path) |
                               generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV stn uvars vars) |
                               generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV stn uvars) |
                               generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV stn) |
                               generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV) |
                               generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV) |
                               generalize (@sym_eval_any typesV funcsV sfuncsV) |
                               generalize (@sym_eval_any typesV funcsV) |
                               generalize (@sym_eval_any typesV)
                             ] *))
                        | (?SF, ?H_interp) =>
                          SEP.reify_sexpr ltac:(isConst) SF typesV funcs pcT stT sfuncs uvars vars 
                          ltac:(fun uvars funcs sfuncs SF =>
                            let funcsV := fresh "funcs" in
                            pose (funcsV := funcs) ;
                            let sfuncsV := fresh "sfuncs" in
                            pose (sfuncsV := sfuncs) ;
                            let proverC := prover typesV funcsV in
                            let proverCV := fresh "proverC" in
                            pose (proverCV := proverC) ;
                            plugin typesV pcT stT funcsV sfuncsV ltac:(fun plugin_syms pluginC =>
                            let pluginCV := fresh "plugin" in
                            pose (pluginCV := pluginC) ;
                            let unfolderC := unfolder typesV pcT stT funcsV sfuncsV in
                            let unfolderCV := fresh "unfolder" in
                            pose (unfolderCV := unfolderC) ;
                            apply (@stateD_proof typesV funcsV sfuncsV (* _ proverCV *)
                              uvars vars _ sp_v rv_v rp_v 
                              sp_pf rv_pf rp_pf pures proofs SF _ (refl_equal _)) in H_interp ;
                            (apply (@Apply_sym_eval typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                              stn uvars vars fin_state st is is_pf) in H_interp ;
                             let syms := constr:((plugin_syms, (typesV, (funcsV, (sfuncsV, (proverCV, (pluginCV, unfolderCV))))))) in
                             finish H_interp syms) || (*fail 100000 "couldn't apply sym_eval_any! (SF case)" || *)
                            first [ 
                              generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                stn uvars vars fin_state st is is_pf) ; idtac "A" |
                              pose is_pf ; generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                stn uvars vars fin_state st is) ; idtac "B" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                  stn uvars) ; idtac "C" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                  stn) ; idtac "D" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV) ; idtac "E" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV) ; idtac "F" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV) ; idtac "G" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV) ; idtac "H" ] 
                            ))
                      end)))))
              end
          end
      end
  end.

Ltac sym_evaluator H := 
  cbv beta iota zeta delta
    [ sym_evalInstrs sym_evalInstr sym_evalLval sym_evalRval sym_evalLoc sym_evalStream sym_assertTest
      sym_setReg sym_getReg
      SepExpr.pures SepExpr.impures SepExpr.other
      SymMem SymRegs SymPures SymVars SymUVars
      SEP.star_SHeap SEP.liftSHeap SEP.multimap_join 
      Expr.SemiDec_expr Expr.expr_seq_dec Expr.tvar_val_sdec Expr.Eq Expr.liftExpr
      app map nth_error value error fold_right hd hd_error tl tail rev
      Decidables.seq_dec 
      DepList.hlist_hd DepList.hlist_tl 
      SepExpr.FM.find SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty SepExpr.FM.fold
      Compare_dec.lt_eq_lt_dec nat_rec nat_rect Peano_dec.eq_nat_dec sumbool_rec sumbool_rect
      EquivDec.equiv_dec EquivDec.nat_eq_eqdec
      f_equal 
      bedrock_funcs_r bedrock_types
      fst snd
      Env.repr Env.updateAt SEP.substV

      stateD Expr.exprD 
      Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation Expr.lookupAs
      Expr.AllProvable Expr.AllProvable_gen Expr.Provable Expr.tvarD
      SEP.sheapD SEP.starred SEP.sexprD
      EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
      Logic.eq_sym eq_sym f_equal
      eq_rec_r eq_rect eq_rec
      nat_rec nat_rect
      sumbool_rec sumbool_rect
      
      SEP.himp SEP.sexprD Expr.Impl 
      Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation 
      Expr.lookupAs
      SepExpr.SDenotation SepExpr.SDomain
      EquivDec.nat_eq_eqdec  
      SEP.sheapD SEP.sepCancel
      SepExpr.impures SepExpr.pures SepExpr.other
      SEP.star_SHeap SEP.unify_remove_all 
      SEP.multimap_join SEP.liftSHeap SEP.unify_remove SEP.starred 
      Expr.tvarD Expr.Eq
      
      SepExpr.FM.fold SepExpr.FM.find SepExpr.FM.add SepExpr.FM.empty 
      bedrock_types 
        
      Compare_dec.lt_eq_lt_dec Peano_dec.eq_nat_dec
      SepExpr.FM.map ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
      ExprUnify.exprUnify ExprUnify.fold_left_2_opt 
      EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
      ExprUnify.get_Eq
      orb
        
      Expr.typeof comparator

      fPlus fMinus fMult
      
      repr_combine default footprint repr' updateAt Default_signature nil_Repr EmptySet_type SEP.Default_ssignature
      bedrock_funcs_r bedrock_types_r

      Summarize Learn Prove
      
      MEVAL.smemeval_read_word MEVAL.smemeval_write_word
      
      EquivDec_nat Peano_dec.eq_nat_dec

      Prover.Prove Prover.Facts Prover.Learn Prover.Summarize
    ] in H.

Implicit Arguments istreamD [ types' ].

Module Demo.
  Require Provers.

  Ltac simplifier H :=
    Provers.unfold_reflexivityProver H ;
    MEVAL.Default.unfolder H ;
    cbv delta [ 
      MEVAL.LearnHook_default
    ] in H; sym_evaluator H.
  
  Definition demo_evaluator ts (fs : functions (repr bedrock_types_r ts)) ps := 
    @MEVAL.Default.MemEvaluator_default_correct _ (tvType 0) (tvType 1) fs ps (settings * state) (tvType 0) (tvType 0) 
    (@IL_mem_satisfies ts)
    (@IL_ReadWord ts)
    (@IL_WriteWord ts).

  Goal forall (cs : codeSpec W (settings * state)) (stn : settings) st st' SF,
    PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) -> 
    Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
    evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' -> 
    Regs st' Rp = natToW 0.
  Proof.
    intros.
    Time sym_eval ltac:(isConst) 
      ltac:(fun ts fs => constr:(@Provers.reflexivityProver_correct ts fs)) (* prover *)
      ltac:(fun ts pc st fs ps k => let res := constr:(@demo_evaluator ts fs ps) in k tt res) (* memory evaluator *)
      ltac:(fun ts pc st fs ps => constr:(@MEVAL.LearnHook_default_correct ts pc st (@SymState ts pc st) (@stateD ts fs ps) fs ps)) (* unfolder *)
      simplifier tt tt tt.
    congruence.
  Qed.
End Demo.

Module UnfolderLearnHook.
  Require Unfolder.

  Module UNF := Unfolder.Make BedrockHeap ST.

  Section typed.
    Variable types : list type.
    Variable hints : UNF.hintsPayload (repr bedrock_types_r types) (tvType 0) (tvType 1).

    Definition unfolder_LearnHook : MEVAL.LearnHook (repr bedrock_types_r types) 
      (SymState (repr bedrock_types_r types) (tvType 0) (tvType 1)) :=
      fun prover st facts => 
        match SymMem st with
          | Some m =>
            match UNF.forward hints prover 10 facts
              {| UNF.Vars := SymVars st 
                ; UNF.UVars := SymUVars st
                ; UNF.Heap := m
              |}
              with
              | {| UNF.Vars := vs ; UNF.UVars := us ; UNF.Heap := m |} =>
                {| SymVars := vs
                 ; SymUVars := us
                 ; SymMem := Some m
                 ; SymRegs := SymRegs st
                 ; SymPures := SymPures st
                |}
            end
          | None => st
        end.

    Variable funcs : functions (repr bedrock_types_r types).
    Variable preds : SEP.sfunctions (repr bedrock_types_r types) (tvType 0) (tvType 1).
    Hypothesis hints_correct : UNF.hintsSoundness funcs preds hints.

    Opaque UNF.forward.

    Theorem unfolderLearnHook_correct 
      : @MEVAL.LearnHook_correct (repr bedrock_types_r types) (tvType 0) (tvType 1) _ (@unfolder_LearnHook) 
        (@stateD _ funcs preds) funcs preds.
    Proof.
      unfold unfolder_LearnHook. econstructor.

      destruct ss; simpl.
      destruct SymMem0; simpl; intros; subst; eauto.
      generalize hints_correct.
      admit.
    Qed.
    Transparent UNF.forward.
  End typed.

  Ltac unfolder_simplifier H := 
    match H with
      | tt => 
        cbv delta [ 
          UNF.Vars UNF.UVars UNF.Heap UNF.Lhs UNF.Rhs
          UNF.Forward
          UNF.forward
          UNF.unfoldForward
          UNF.findWithRest UNF.find 
          equiv_dec
          UNF.substExpr
          Unfolder.FM.add

          impures pures other
          
          Unfolder.allb 

          length map app
          exprSubstU
          
          ExprUnify.exprUnifyArgs ExprUnify.empty_Subst 

          unfolder_LearnHook
          UNF.default_hintsPayload
          UNF.fmFind
          UNF.findWithRest'
        ]
      | _ => 
        cbv delta [ 
          UNF.Vars UNF.UVars UNF.Heap UNF.Lhs UNF.Rhs
          UNF.Forward
          UNF.forward
          UNF.unfoldForward
          UNF.findWithRest UNF.find 
          equiv_dec
          UNF.substExpr
          Unfolder.FM.add

          impures pures other
          
          Unfolder.allb 

          length map app
          exprSubstU

          ExprUnify.exprUnifyArgs ExprUnify.empty_Subst 

          unfolder_LearnHook
          UNF.default_hintsPayload
          UNF.fmFind
          UNF.findWithRest'
        ] in H
    end.

  (** This ltac builds an unfolder given a hint database.
   ** [hints] is a gallina term of type [forall ts fs pcT stT ps, UNF.hintsSoundness ts fs pcT stT ps H]
   **   if [H] is the hints to use in unfolding
   **)
  Ltac unfolder_for hints :=
    fun ts pc st fs ps => constr:(@unfolderLearnHook_correct ts _ fs ps (hints ts fs (tvType 0) (tvType 1) ps)).
      
  Goal forall (cs : codeSpec W (settings * state)) (stn : settings) st st' SF,
    PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) -> 
    Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
    evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' -> 
    Regs st' Rp = natToW 0.
  Proof.
    intros.
    Time sym_eval ltac:(isConst) 
      ltac:(fun ts fs => constr:(@Provers.reflexivityProver_correct ts fs)) (* prover *)
      ltac:(fun ts pc st fs ps k => let res := constr:(@Demo.demo_evaluator ts fs ps) in k tt res) (* memory evaluator *)
      ltac:(unfolder_for (@UNF.hintsSoundness_default)) (* unfolder *)
      ltac:(fun H => Provers.unfold_reflexivityProver H ; MEVAL.Default.unfolder H ; unfolder_simplifier H ; sym_evaluator H)
      tt tt tt.
    congruence.
  Qed.

End UnfolderLearnHook.

Module PluginEvaluator.
  
  Definition plugin_evaluator ts (fs : functions (repr bedrock_types_r ts)) ps evals consistent_pf := 
    @MEVAL.Plugin.CompositeMemEvaluator_correct _ (tvType 0) (tvType 1) evals fs ps (settings * state) (tvType 0) (tvType 0)
    (@IL_mem_satisfies ts)
    (@IL_ReadWord ts)
    (@IL_WriteWord ts)
    consistent_pf.

  (** This Ltac builds a function that can be instantiated to build a composite evaluator.
   ** It should be applied to one argument and passed as the 3rd argument to [sym_eval].
   ** Arguments:
   ** - [known] is a tuple of [forall ts fs, @MemEvalPred_correct ts ? (tvType 0) (tvType 1) ? (tvType 0) (tvType 0) ... ]
   **)
  Ltac composite_eval known :=
    let rec find_in p ls acc :=
      match ls with
        | nil => fail 100000 " didn't find " p
        | ?l :: ?ls =>
          match Reflect.unifies (SDenotation l) p with
            | true => acc
            | false => 
              find_in p ls (S acc)
          end
      end
    in
    fun ts _pc _st fs ps k =>
      let psVal := eval unfold ps in ps in
      let rec build_pf known k :=
        match known with
          | tt => 
            let r := constr:(@nil (nat * MEVAL.Plugin.MemEvalPred ts)) in
            let pf := constr:(I) in
            k r pf
          | (?L, ?known) =>
            let Z := type of L in
            match type of L with
              | forall ts,  forall fs, @MEVAL.Plugin.MemEvalPred_correct _ _ _ _ _ _ _ _ _ _ (@?s ts) _ =>
                let p := eval simpl SDenotation in (SDenotation (s ts)) in
                let idx := find_in p psVal 0 in                  
                build_pf known ltac:(fun res pf =>
                  let ZZZ := constr:(@L ts fs) in
                  let E :=
                    match type of ZZZ with
                      | @MEVAL.Plugin.MemEvalPred_correct _ ?P _ _ _ _ _ _ _ _ _ _ => P
                    end
                  in
                  let f := constr:((idx, E) :: res) in
                  let pf := constr:(@conj _ _ ZZZ pf) in
                  k f pf)              
            end
        end
      in 
      build_pf known ltac:(fun evals consistent_pf =>
        let evalsV := fresh "evals" in
        pose (evalsV := evals) ;
        let consistentV := fresh "consistent" in
        let res := constr:(@plugin_evaluator ts fs ps evalsV consistent_pf) in
        k evalsV res).

 Goal forall (cs : codeSpec W (settings * state)) (stn : settings) st st' SF,
    PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) -> 
    Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
    evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' -> 
    Regs st' Rp = natToW 0.
  Proof.
    intros.
    Time sym_eval ltac:(isConst) 
      ltac:(fun ts fs => constr:(@Provers.reflexivityProver_correct ts fs)) (* prover *)
      ltac:(composite_eval tt) (* memory evaluator *)
      ltac:(UnfolderLearnHook.unfolder_for (@UnfolderLearnHook.UNF.hintsSoundness_default)) (* unfolder *)
      ltac:(fun H => Provers.unfold_reflexivityProver H ; MEVAL.Default.unfolder H ; UnfolderLearnHook.unfolder_simplifier H ; sym_evaluator H)
      tt tt tt.
    congruence.
  Qed.

End PluginEvaluator.