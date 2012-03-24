(** This file implements symbolic evaluation for the
 ** language defined in IL.v
 **)
Require Import IL SepIL.
Require Import Word Memory.
Require Import DepList EqdepClass.
Require Import PropX.
Require Expr SepExpr.
Import List.

Require Structured SymEval.

Set Implicit Arguments.
Set Strict Implicit.

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
  :: {| Expr.Impl := state 
      ; Expr.Eq := fun _ _ => None
      |}
  :: {| Expr.Impl := IL.test
      ; Expr.Eq := fun l r => 
        match l as l , r as r with
          | IL.Eq , IL.Eq => Some (refl_equal _)
          | IL.Ne , IL.Ne => Some (refl_equal _)
          | IL.Le , IL.Le => Some (refl_equal _)
          | IL.Lt , IL.Lt => Some (refl_equal _)
          | _ , _ => None
        end
      |}
  :: {| Expr.Impl := IL.reg
      ; Expr.Eq := fun l r =>
        match l as l , r as r with
          | IL.Sp , IL.Sp => Some (refl_equal _)
          | IL.Rp , IL.Rp => Some (refl_equal _)
          | IL.Rv , IL.Rv => Some (refl_equal _)
          | _ , _ => None
        end |}
  :: nil.

Definition bedrock_ext (ls : list Expr.type) : list Expr.type :=
  match ls with
    | _ :: _ :: _ :: _ :: _ :: r => r
    | _ => nil
  end.

(** Symbolic Evaluation **)
Module PLUGIN := SymEval.EvaluatorPlugin BedrockHeap ST.

Module BedrockEvaluator.
  Require Import SepExpr SymEval.
  Require Import Expr.

  Module SEP := PLUGIN.SEP.

  Section typed.
    Context {types : list type}.
   
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

  End typed.

  Implicit Arguments sym_loc [ ].
  Implicit Arguments sym_lvalue [ ].
  Implicit Arguments sym_rvalue [ ].
  Implicit Arguments sym_instr [ ].
  Implicit Arguments sym_assert [ ].

  Definition comparator (t : IL.test) (l r : W) : Prop :=
    match t with
      | IL.Eq => l = r
      | IL.Ne => l = r -> False
      | IL.Lt => wlt l r
      | IL.Le => wlt l r \/ l = r
    end.

  Definition pcT := tvType 0.
  Definition tvWord := tvType 0.
  Definition stT := tvType 1.
  Definition tvState := tvType 2.
  Definition tvTest := tvType 3.
  Definition tvReg := tvType 4.

  Definition bedrock_funcs typs : list (signature (bedrock_types ++ typs)).
  refine ({| Domain := tvWord :: tvWord :: nil
           ; Range := tvWord
           ; Denotation := _ |} ::
          {| Domain := tvWord :: tvWord :: nil
           ; Range := tvWord
           ; Denotation := _ |} ::
          {| Domain := tvWord :: tvWord :: nil
           ; Range := tvWord
           ; Denotation := _ |} ::
          {| Domain := tvTest :: tvWord :: tvWord :: nil
           ; Range := tvProp
           ; Denotation := _ |} :: 
          {| Domain := tvState :: tvReg :: nil
           ; Range := tvWord
           ; Denotation := _ |} :: nil).
  refine (@wplus 32).
  refine (@wminus 32).
  refine (@wmult 32).
  refine comparator.
  refine Regs.
  Defined.

  Section typed_ext.
    Variable types' : list type.
    Definition types := bedrock_types ++ types'.

  
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

    Variable funcs' : functions types.
    Definition funcs := bedrock_funcs types' ++ funcs'.

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

    Variable Facts : Type.
    Variable learnFacts : Facts -> list (expr types) -> Facts.

    (** Symbolic State **)
    Record SymState : Type :=
    { SymMem   : SEP.SHeap types pcT stT
    ; SymRegs  : SymRegType
    ; SymPures : list (expr types)
    ; SymFacts : Facts
    }.

    Variable symeval_read_word : Facts -> expr types -> SEP.SHeap types pcT stT 
      -> option (expr types).
    Variable symeval_write_word : Facts -> expr types -> expr types -> SEP.SHeap types pcT stT 
      -> option (SEP.SHeap types pcT stT).
    
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
          Some {| SymMem := SymMem ss 
                ; SymRegs := sym_setReg r val (SymRegs ss)
                ; SymPures := SymPures ss
                ; SymFacts := SymFacts ss |}
        | SymLvMem l => 
          let l := sym_evalLoc l ss in
            match symeval_write_word (SymFacts ss) l val (SymMem ss) with
              | Some m =>
                Some {| SymMem := m ; SymRegs := SymRegs ss ; SymPures := SymPures ss ; SymFacts := SymFacts ss |}
              | None => None
            end
      end.

    Definition sym_evalRval (rv : sym_rvalue types) (ss : SymState) : option (expr types) :=
      match rv with
        | SymRvLval (SymLvReg r) =>
          Some (sym_getReg r (SymRegs ss))
        | SymRvLval (SymLvMem l) =>
          let l := sym_evalLoc l ss in
          symeval_read_word (SymFacts ss) l (SymMem ss)
        | SymRvImm w => Some w 
        | SymRvLabel l => None (* TODO: can we use labels? it seems like we need to reflect these as words. *)
        (* an alternative would be to reflect these as a function call that does the positioning...
         * - it isn't clear that this can be done since the environment would need to depend on the settings.
         *)
        (*Some (Expr.Const (types := types) (t := tvType 2) l) *)
      end.

    Definition sym_assertTest (r : sym_rvalue types) (t : test) (l : sym_rvalue types) (ss : SymState) (res : bool) 
      : option (expr types) :=
      match sym_evalRval l ss , sym_evalRval r ss with
        | Some l , Some r =>
          Some (Expr.Func 3 (Expr.Const (types := types) (t := tvTest) t :: l :: r :: nil))
        | _ , _ => None
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

    Fixpoint sym_evalInstrs (is : list (sym_instr types)) (ss : SymState) 
      : SymState + (SymState * list (sym_instr types)) :=
      match is with
        | nil => inl ss
        | i :: is =>
          match sym_evalInstr i ss with
            | None => inr (ss, i :: is)
            | Some ss => sym_evalInstrs is ss
          end
      end.

    Definition istream : Type := list (sym_instr types + sym_assert types).

    Fixpoint sym_evalStream (is : istream) (ss : SymState) : option SymState + (SymState * istream) :=
      match is with
        | nil => inl (Some ss)
        | inl i :: is =>
          match sym_evalInstr i ss with
            | None => inr (ss, inl i :: is)
            | Some ss => sym_evalStream is ss
          end
        | inr asrt :: is =>
          match asrt with
            | SymAssertCond l t r (Some res) =>
              match sym_assertTest l t r ss res with
                | Some sp => 
                  let ss' :=
                    {| SymRegs := SymRegs ss 
                     ; SymMem := SymMem ss
                     ; SymPures := sp :: SymPures ss
                     ; SymFacts := learnFacts (SymFacts ss) (sp :: nil)
                     |}
                  in
                  sym_evalStream is ss'
                | None => inr (ss, inr asrt :: is)
              end
            | SymAssertCond l t r None =>
              match sym_evalRval l ss , sym_evalRval r ss with
                | None , _ => inl None
                | _ , None => inl None
                | _ , _ => sym_evalStream is ss 
              end
          end
      end.

    (* Denotation functions *)
    Section sym_denote.
      Variable funcs : functions types.
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

      Variable sfuncs : SEP.sfunctions types pcT stT.

      Definition stateD cs (stn : IL.settings) (s : state) (ss : SymState) : Prop :=
        match ss with
          | {| SymMem := m ; SymRegs := (sp, rp, rv) ; SymPures := pures |} =>
            match 
             exprD funcs uvars vars sp tvWord ,
             exprD funcs uvars vars rp tvWord ,
             exprD funcs uvars vars rv tvWord
            with
              | Some sp , Some rp , Some rv =>
                Regs s Sp = sp /\ Regs s Rp = rp /\ Regs s Rv = rv
              | _ , _ , _ => False
            end
            /\ PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD m)) (stn, s))%PropX
            /\ AllProvable funcs uvars vars pures 
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
(*
      Lemma stateD_proof : forall (st : state) (sp rv rp : Expr.expr types),
        Expr.exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
        Expr.exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
        Expr.exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
        forall (pures : list (expr types)), 
          AllProvable funcs uvars vars pures ->
        forall sh (hashed : SEP.SHeap types pcT stT),
          SEP.hash sh = (nil , hashed) ->
          forall (cs : codeSpec W (settings * state)) (stn : settings),
          interp cs (![@SEP.sexprD types funcs pcT stT sfuncs uvars vars sh] (stn, st)) ->
          stateD cs stn st {| SymMem := hashed; SymRegs := (sp, rp, rv) ; SymPures := nil |}.
      Proof.
        clear. intros. simpl. rewrite H. rewrite H0. rewrite H1.
        intuition. eapply hash_interp; eauto.
      Qed.
*)
      Fixpoint evalPath (stn : settings) (is : list (sym_instr types + sym_assert types))
        (st : state) (st' : option state) : Prop :=
        match is with 
          | nil => Some st = st'
          | inl i :: is =>
            match sym_instrD i with
              | None => False
              | Some i => 
                match evalInstr stn st i with
                  | None => st' = None
                  | Some st'' => evalPath stn is st'' st'
                end
            end
          | inr a :: is =>
            match a with
              | SymAssertCond l t r None => 
                st' = None
              | SymAssertCond l t r (Some res) => 
                match sym_rvalueD l , sym_rvalueD r with
                  | Some l , Some r =>
                    Structured.evalCond l t r stn st <> None /\
                    evalPath stn is st st'
                  | _ , _ => False
                end
            end
        end.

      Theorem evalPath_instrs : forall (stn : settings) (sis : list (sym_instr types)),
        match sym_instrsD sis with
          | None => True
          | Some is =>
            forall st res, 
            evalInstrs stn st is = res ->
            evalPath stn (map (@inl _ _) sis) st res
        end.
      Proof.
        clear. induction sis; simpl; auto.
        case_eq (sym_instrD a); intros; auto.
        revert IHsis. case_eq (sym_instrsD sis); auto.
        simpl. intros. 
        destruct (evalInstr stn st i); intros; auto.
      Qed.

      Theorem evalPath_cond : forall stn (l' r' : sym_rvalue types) (t : test) ,
        match sym_rvalueD l' , sym_rvalueD r' with
          | Some l , Some r =>
            forall st b,
              Structured.evalCond l t r stn st = b ->
              match b with
                | None => 
                  evalPath stn (inr (SymAssertCond l' t r' b) :: nil) st None
                | Some b' =>
                  evalPath stn (inr (SymAssertCond l' t r' (Some b')) :: nil) st (Some st)
              end
          | _ , _ => True
        end.
      Proof.
        clear. intros. 
        case_eq (sym_rvalueD l'); auto.
        case_eq (sym_rvalueD r'); auto. intros.
        simpl. unfold Structured.evalCond in *.
        destruct b; auto; simpl.
        rewrite H. rewrite H0.
        repeat match goal with
                 | [ H : match ?X with 
                           | Some _ => _
                           | None => _
                         end = _ |- _ ] => destruct X; auto
               end; try congruence.
        intuition; congruence.
      Qed.        

      Theorem evalPath_app : forall stn a st st' b r, 
        evalPath stn a st (Some st') ->
        evalPath stn b st' r ->
        evalPath stn (a ++ b) st r.
      Proof.
        clear. induction a; simpl; intros; auto.
          inversion H; auto.
          
          destruct a.
          repeat match goal with
                   | [ H : match ?X with 
                             | Some _ => _ 
                             | None => _
                           end |- _ ] => destruct X ; try congruence
                 end; eauto.
          destruct s; destruct o; try congruence.
          destruct (sym_rvalueD s); auto.
          destruct (sym_rvalueD s0); auto. intuition eauto.
      Qed.        
      
      Theorem evalPath_nil : forall stn st,
        evalPath stn nil st (Some st).
      Proof.
        clear; simpl; auto.
      Qed.
    End sym_denote.

    Theorem evalPath_ext : forall fs fs' uvars vars stn a st st',
      evalPath fs uvars vars stn a st st' ->
      evalPath (fs ++ fs') uvars vars stn a st st'.
    Proof.
      clear. induction a; simpl; intros; auto.
    Admitted.

    Theorem evalPath_instrs_app : forall fs fs' uvars vars sis stn a st st',
      evalPath fs uvars vars stn a st (Some st') ->
      match sym_instrsD (fs ++ fs') uvars vars sis with
        | None => True
        | Some is =>
          forall some_or_none, 
            evalInstrs stn st' is = some_or_none ->
            evalPath (fs ++ fs') uvars vars stn (a ++ map (@inl _ _) sis) st some_or_none
      end.
    Proof.
      clear. intros.
      generalize (evalPath_instrs (fs ++ fs') uvars vars stn sis).
      destruct (sym_instrsD (fs ++ fs') uvars vars sis); intros; auto.
      eapply evalPath_app; eauto.
      eapply evalPath_ext; auto.
    Qed.

    Theorem evalPath_cond_app : forall fs fs' uvars vars l t r stn a st st',
      evalPath fs uvars vars stn a st (Some st') ->
      match sym_rvalueD (fs ++ fs') uvars vars l , sym_rvalueD (fs ++ fs') uvars vars r with
        | Some l' , Some r' =>
          forall some_or_none, 
            Structured.evalCond l' t r' stn st' = some_or_none ->
            match some_or_none with
              | None => 
                evalPath (fs ++ fs') uvars vars stn (a ++ inr (SymAssertCond l t r some_or_none) :: nil) st None
              | _ => 
                evalPath (fs ++ fs') uvars vars stn (a ++ inr (SymAssertCond l t r some_or_none) :: nil) st (Some st')
            end
        | _ , _ => True
      end.
    Proof.
      clear. intros.
      generalize (evalPath_cond (fs ++ fs') uvars vars stn l r t).
      destruct (sym_rvalueD (fs ++ fs') uvars vars l); auto;
      destruct (sym_rvalueD (fs ++ fs') uvars vars r); auto.
      intros. eapply H0 in H1. destruct some_or_none;
      eapply evalPath_app; try solve [ eauto | eapply evalPath_ext; eauto ]. 
    Qed.      

  End typed_ext.

  Section correctness.
    Record Correctness
      (Facts : Type)
      (Learn : forall typs, Facts -> list (expr (bedrock_types ++ typs)) -> Facts)
      (symeval_read_word : forall typs, Facts -> expr (bedrock_types ++ typs) ->
        SEP.SHeap (bedrock_types ++ typs) pcT stT -> option (expr (bedrock_types ++ typs))) 
      (symeval_write_word : forall typs, Facts -> expr (bedrock_types ++ typs) -> expr (bedrock_types ++ typs) ->
        SEP.SHeap (bedrock_types ++ typs) pcT stT -> 
        option (SEP.SHeap (bedrock_types ++ typs) pcT stT))
      : Type :=
    { TypeImage : list (nat * type)
    ; FuncImage : forall typs, list (nat * signature (bedrock_types ++ Env.repr TypeImage typs))
    ; PredImage : forall typs, list (nat * SEP.ssignature (bedrock_types ++ Env.repr TypeImage typs) pcT stT)
    ; Valid : forall types_ext, 
      env (bedrock_types ++ Env.repr TypeImage types_ext) ->
      env (bedrock_types ++ Env.repr TypeImage types_ext) ->
      Facts -> Prop
    ; ReadCorrect :
      forall types_ext,
        let types_ext' := Env.repr TypeImage types_ext in
        let types := bedrock_types ++ types_ext' in
        forall (funcs_ext : functions types) (sfuncs_ext : SEP.sfunctions types pcT stT),
          let funcs := bedrock_funcs (Env.repr TypeImage types_ext) ++ Env.repr (FuncImage types_ext) funcs_ext in
          let sfuncs := Env.repr (PredImage types_ext) sfuncs_ext in
          forall hyps pe ve SH,
            symeval_read_word types_ext' hyps pe SH = Some ve ->
            forall uvars vars cs p m stn,
            Valid _ uvars vars hyps ->
            exprD funcs uvars vars pe tvWord = Some p ->
            PropX.interp cs (![ SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD SH) ] (stn, m)) ->
            match exprD funcs uvars vars ve tvWord with
              | Some v =>
                ReadWord stn (Mem m) p = Some v
              | _ => False
            end
    ; WriteCorrect :
      forall types_ext,
        let types_ext' := Env.repr TypeImage types_ext in
        let types := bedrock_types ++ types_ext' in
        forall (funcs_ext : functions types) (sfuncs_ext : SEP.sfunctions types pcT stT),
          let funcs := bedrock_funcs (Env.repr TypeImage types_ext) ++ Env.repr (FuncImage types_ext) funcs_ext in
          let sfuncs := Env.repr (PredImage types_ext) sfuncs_ext in
          forall uvars vars cs hyps pe ve m stn SH SH',
            symeval_write_word types_ext' hyps pe ve SH = Some SH' ->
            Valid _ uvars vars hyps ->
            forall p v,
            exprD funcs uvars vars pe tvWord = Some p ->
            exprD funcs uvars vars ve tvWord = Some v ->
            PropX.interp cs (![ SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD SH) ] (stn, m)) ->
            match mem_set_word _ _ (footprint_w) (BedrockHeap.mem_set) (explode stn) p v (Mem m) with
              | None => False
              | Some m' =>
                PropX.interp cs (![ SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD SH') ] (stn, {| Regs := Regs m ; Mem := m' |}))
            end
    }.

    Theorem sym_eval_any F L symeval_read_word symeval_write_word 
      (C : @Correctness F L symeval_read_word symeval_write_word) :
      forall types_ext,
        let types' := Env.repr (TypeImage C) types_ext in
        let types := bedrock_types ++ types' in
        forall (funcs_ext : functions types) (sfuncs_ext : SEP.sfunctions types pcT stT),
          let funcs := bedrock_funcs (Env.repr (TypeImage C) types_ext) ++ Env.repr (FuncImage C types_ext) funcs_ext in
          let sfuncs := Env.repr (PredImage C types_ext) sfuncs_ext in
      forall stn uvars vars sound_or_safe st p,
        evalPath funcs uvars vars stn p st sound_or_safe ->
        forall cs ss,
        stateD funcs uvars vars sfuncs cs stn st ss ->
        let res := @sym_evalStream _ F (L _) (symeval_read_word _) (symeval_write_word _) p ss in
        match sound_or_safe with
          | None =>
            (** safe **)
            match res with
              | inl None => True
              | inl (Some _) => False
              | inr (ss'', is') => True (*
                exists st'' : state,
                  match sym_instrsD is' with
                    | Some instrs' =>
                      evalInstrs stn st'' instrs' = None /\
                      stateD cs stn st'' ss''
                    | None => False
                  end
*)
            end
          | Some st' =>
            (** correct **)
            match res with
              | inl None => False                
              | inl (Some ss') => stateD funcs uvars vars sfuncs cs stn st' ss'
              | inr (ss'', is') => True (*
                exists st'' : state,
                  match sym_instrsD is' with
                    | Some instrs' =>
                      evalInstrs stn st'' instrs' = Some st' /\
                      stateD cs stn st'' ss''
                    | None => False
                  end
*)
            end
        end.
    Proof.

(*
        repeat match goal with
                 | [ H : match ?X with
                           | inl _ => _
                           | inr _ => _
                         end |- _ ] => revert H; case_eq X; intros; subst
                 | [ H : match ?X with
                           | Some _ => _
                           | None => _
                         end |- _ ] => revert H; case_eq X; intros; subst
                 | [ |- match match ?X with 
                                | Some _ => _ 
                                | None => _ 
                              end with
                          | inl _ => _
                          | inr _ => _
                        end ] => destruct X
                 | [ |- match ?X with
                          | Some _ => _
                          | None => _
                        end ] => destruct X
                 | [ |- match ?X with
                          | inl _ => _
                          | inr _ => _
                        end ] => destruct X
                 | [ |- match ?X with 
                          | (_,_) => _
                        end ] => destruct X
               end; auto.
*)
    Admitted.
    
  End correctness.

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

Lemma interp_interp_cancel : forall types',
  let types := app bedrock_types types' in
    forall funcs sfuncs (eq_prover : Provers.EqProverT funcs) uvars vars L stn_st cs,
      interp cs (![ (@SEP.sexprD types funcs pcT stT sfuncs uvars vars (SEP.sheapD L))] stn_st) ->
      forall hyps, AllProvable funcs uvars vars hyps ->
      forall SF R,
        SEP.hash SF = (nil, R) ->
        forall funcs' sfuncs',
          match SEP.sepCancel eq_prover hyps L R with
            | (L , R , subst_L , subst_R) =>
              SEP.himp funcs sfuncs uvars uvars vars cs (SEP.sheapD L) (SEP.sheapD R)
          end    
          -> interp cs (![ @SEP.sexprD types (app funcs funcs') pcT stT (app sfuncs sfuncs') uvars vars SF ] stn_st).
Proof.
  clear. intros.
  unfold himp in *. 
  generalize (@SEP.hash_denote _ funcs0 pcT stT sfuncs cs SF uvars vars).
Admitted.

Require Import Provers.

Theorem stateD_proof : forall (types' : list Expr.type)
  (funcs : Expr.functions (types types'))
  (P : EqProverT funcs)
  (uvars vars : Expr.env (types types'))
  (sfuncs : SEP.sfunctions (types types') pcT stT) 
  (st : state) (sp rv rp : Expr.expr (types types')),
  Expr.exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
  Expr.exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
  Expr.exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
  forall pures : list (Expr.expr (types types')),
    Expr.AllProvable funcs uvars vars pures ->
    forall (sh : SEP.sexpr (types types') pcT stT)
      (hashed : SEP.SHeap (types types') pcT stT),
      SEP.hash sh = (nil, hashed) ->
      forall (cs : codeSpec W (settings * state)) (stn : settings),
        interp cs (![SEP.sexprD funcs sfuncs uvars vars sh] (stn, st)) ->
        stateD funcs uvars vars sfuncs cs stn st
        {| SymMem := hashed; SymRegs := (sp, rp, rv); SymPures := pures
         ; SymFacts := eq_summarize P pures
         |}.
Proof.
  unfold stateD. intros.
  rewrite H. rewrite H1. rewrite H0.
  intuition auto.
  eapply hash_interp; eauto.
Qed.

Theorem sym_eval_any_raw : forall F L
  (symeval_read_word : forall typs : list Expr.type,
    list (Expr.expr (bedrock_types ++ typs)) ->
    Expr.expr (bedrock_types ++ typs) ->
    SEP.SHeap (bedrock_types ++ typs) pcT stT ->
    option
    (Expr.expr (bedrock_types ++ typs)))
  (symeval_write_word : forall typs : list Expr.type,
    list (Expr.expr (bedrock_types ++ typs)) ->
    Expr.expr (bedrock_types ++ typs) ->
    Expr.expr (bedrock_types ++ typs) ->
    SEP.SHeap (bedrock_types ++ typs) pcT
    stT ->
    option
    (SEP.SHeap (bedrock_types ++ typs) pcT
      stT))
  (C : Correctness F L symeval_read_word symeval_write_word)
  (types_ext : list Expr.type),
  let types' := Env.repr (TypeImage C) types_ext in
    let types := (bedrock_types ++ types')%list in
      forall (funcs_ext : Expr.functions types)
        (sfuncs_ext : SEP.sfunctions types pcT stT),
        let funcs :=
          (bedrock_funcs types' ++
            Env.repr (FuncImage C types_ext) funcs_ext)%list in
          let sfuncs := Env.repr (PredImage C types_ext) sfuncs_ext in
            forall (P : EqProverT funcs) (uvars vars : Expr.env types)
              (sound_or_safe : option state) (stn : settings) (st : state)
              (p : list (sym_instr types + sym_assert types)),
              evalPath funcs uvars vars stn p st sound_or_safe ->
              forall (sp rv rp : Expr.expr types),
                Expr.exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
                Expr.exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
                Expr.exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
                forall pures : list (Expr.expr types),
                  Expr.AllProvable funcs uvars vars pures ->
                  forall sh hashed,
                    SEP.hash sh = (nil, hashed) ->
                    forall (cs : codeSpec W (settings * state)),
                      interp cs (![SEP.sexprD funcs sfuncs uvars vars sh] (stn, st)) ->
                      let ss := {| SymMem := hashed; SymRegs := (sp, rp, rv); SymPures := pures |} in
                        let res :=
                          sym_evalStream
                          (symeval_read_word (Env.repr (TypeImage C) types_ext))
                          (symeval_write_word (Env.repr (TypeImage C) types_ext)) p ss in
                          match sound_or_safe with
                            | Some st' =>
                              match res with
                                | inl (Some ss') => stateD funcs uvars vars sfuncs cs stn st' ss'
                                | inl None => False
                                | inr (_, _) => True
                              end
                            | None =>
                              match res with
                                | inl (Some _) => False
                                | inl None => True
                                | inr (_, _) => True
                              end
                          end.
Proof.
  intros. eapply sym_eval_any with (C := C) (st := st); eauto.
  unfold ss in *.
  eapply stateD_proof; eauto.
Qed.




  (** Reflection **)

  (* Reflect the instructions *)
  Ltac collectTypes_loc isConst l Ts :=
    match l with
      | Reg _ => Ts
      | Imm ?i => collectTypes_expr isConst i Ts
      | Indir _ ?i => collectTypes_expr isConst i Ts
    end.
  Ltac reflect_loc isConst l types funcs uvars vars k :=
    match l with
      | Reg ?r => constr:(@SymReg types r)
      | Imm ?i =>
        reflect_expr isConst i types funcs uvars vars ltac:(fun funcs i =>
          let l := constr:(@SymImm types i) in k funcs l)
      | Indir ?r ?i =>
        reflect_expr isConst i types funcs uvars vars ltac:(fun funcs i =>
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
      | RvImm ?i => collectTypes_expr isConst i Ts
      | RvLabel _ => let l := constr:(label:Type) in Reflect.cons_uniq l Ts
    end.

  Ltac reflect_rvalue isConst r types funcs uvars vars k :=
    match r with
      | RvLval ?l =>
        reflect_lvalue isConst l types funcs uvars vars ltac:(fun funcs l =>
          let l := constr:(@SymRvLval types l) in k funcs l)
      | RvImm ?i =>
        reflect_expr isConst i types funcs uvars vars ltac:(fun funcs i =>
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

  Ltac open_stateD H0 :=
    cbv beta iota zeta delta 
      [ stateD Expr.exprD Expr.applyD
        EquivDec.equiv_dec 
        Expr.Range Expr.Domain Expr.Denotation
        Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
        sumbool_rec sumbool_rect
        Peano_dec.eq_nat_dec nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym
        nth_error map value
        tvWord
        f_equal

        Expr.AllProvable Expr.Provable Expr.tvarD tvTest types comparator
      ] in H0; 
      let a := fresh in 
      let b := fresh in
      let zz := fresh in destruct H0 as [ a [ b zz ] ] ;
      destruct a as [ ? [ ? ? ] ];
      repeat match type of zz with
               | True => clear zz
               | _ /\ _ => let v := fresh in destruct zz as [ v zz ]
             end.
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
   ** - [unfolder] needs to unfold the definitions in [C]
   ** - [C] is the [Correctness] record
   ** - [Ts] is a list of types, i.e. type [list Type] or tt
   ** - [Fs] is a tuple of functions, [tt] is interpreted as a unit
   ** - [SFs] is a tuple of separation logic predicates, [tt] is interpreted as a unit
   **)
  Ltac sym_eval isConst prover simplifier C Ts Fs SFs :=
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
    in
    let rec collectAllTypes_instrs is Ts :=
      match is with
        | tt => Ts
        | (((?l,?r), _), ?is) =>
          let Ts := collectTypes_rvalue ltac:(isConst) l Ts in
          let Ts := collectTypes_rvalue ltac:(isConst) r Ts in
          collectAllTypes_instrs is Ts
        | ((?i, _), ?is) =>
          let Ts := collectTypes_instrs ltac:(isConst) i Ts in
          collectAllTypes_instrs is Ts
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
                    let all_instrs := get_instrs st tt in
                    let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
                    (** collect the raw types **)
                    let Ts := collectAllTypes_instrs all_instrs Ts in
                    let Ts := Expr.collectAllTypes_expr ltac:(isConst) Ts regs in
                    let Ts := SEP.collectAllTypes_sexpr isConst Ts (SF :: nil) in
                    let Ts := Expr.collectAllTypes_funcs Ts Fs in
                    let Ts := SEP.collectAllTypes_sfuncs Ts SFs in
                    let Ts := Expr.collectAllTypes_props shouldReflect isConst Ts in
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
                    let types_ext := eval simpl in (bedrock_ext types_) in
                    let types_extV := fresh "types_ext" in
                    pose (types_extV := types_ext);
                    (** build the variables **)
                    let uvars := eval simpl in (@nil _ : Expr.env typesV) in
                    let vars := eval simpl in (@nil _ : Expr.env typesV) in
                    (** build the base functions **)
                    let funcs := eval unfold bedrock_funcs in (bedrock_funcs types_extV) in
                    let funcs := Expr.getAllFunctions typesV funcs Fs in
                    let funcs := eval simpl in funcs in
                    (** build the base sfunctions **)
                    let sfuncs := constr:(@nil (@SEP.ssignature typesV pcT stT)) in
                    let sfuncs := SEP.getAllSFunctions pcT stT typesV sfuncs SFs in
                    (** reflect the expressions **)
                    let rec build_path instrs last funcs k :=
                      match instrs with
                        | tt => k funcs last
                        | ((?i, ?H), ?is) =>
                          match type of H with
                            | Structured.evalCond ?l ?t ?r _ ?st = _ =>
                              reflect_rvalue ltac:(isConst) l typesV funcs uvars vars ltac:(fun funcs' l =>
                              reflect_rvalue ltac:(isConst) r typesV funcs' uvars vars ltac:(fun funcs' r =>
                                let funcs_ext := Reflect.extension funcs funcs' in
                                eapply (@evalPath_cond_app types_extV funcs funcs_ext uvars vars l t r _ _ _ _ last) in H;
                                cbv iota in H ;
                                clear last ; 
                                build_path is H funcs' k))
                            | evalInstrs _ ?st _ = _ =>
                              reflect_instrs ltac:(isConst) i typesV funcs uvars vars ltac:(fun funcs' sis =>
                                let funcs_ext := Reflect.extension funcs funcs' in
                                eapply (@evalPath_instrs_app types_extV funcs funcs_ext uvars vars sis _ _ _ _ last) in H ; 
                                clear last ;
                                build_path is H funcs' k)
                          end
                      end
                    in
                    Expr.reflect_props shouldReflect ltac:(isConst) typesV funcs uvars vars ltac:(fun funcs pures proofs =>
                    Expr.reflect_expr ltac:(isConst) rp_v typesV funcs uvars vars ltac:(fun funcs rp_v =>
                    Expr.reflect_expr ltac:(isConst) sp_v typesV funcs uvars vars ltac:(fun funcs sp_v =>
                    Expr.reflect_expr ltac:(isConst) rv_v typesV funcs uvars vars ltac:(fun funcs rv_v =>
                    SEP.reflect_sexpr ltac:(isConst) SF typesV funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
                    generalize (@evalPath_nil types_extV funcs uvars vars stn st) ;
                    let starter := fresh in
                    intro starter ;
                    let funcs := eval simpl app in funcs in
                    build_path all_instrs starter funcs ltac:(fun funcs path =>
                      match funcs with
                        | _ :: _ :: _ :: _ :: _ :: ?funcs_ext => idtac ;
                          apply (@stateD_proof types_ext funcs uvars vars sfuncs _ sp_v rv_v rp_v 
                            sp_pf rv_pf rp_pf pures proofs SF _ (refl_equal _)) in H' ;
                          apply (@sym_eval_any _ _ C types_ext funcs_ext sfuncs stn uvars vars _ _ _ path) in H' ;
                          clear path ;
                          (simplifier H' || fail 1000000 "simplifier failed!") ;
                          subst typesV; subst types_extV ;
                          (try assumption ||
                           destruct H' as [ [ ? [ ? ? ] ] [ ? ? ] ])
                      end))))))
                end
            end
        end
    end.
  
  Ltac sym_evaluator H := 
    cbv beta iota zeta delta
      [ sym_evalInstrs sym_evalInstr sym_evalLval sym_evalRval sym_evalLoc sym_evalStream sym_assertTest
        sym_setReg sym_getReg
        SepExpr.pures SepExpr.impures SepExpr.other
        SymMem SymRegs SymPures
        SEP.star_SHeap SEP.liftSHeap SEP.multimap_join 
        Expr.SemiDec_expr Expr.expr_seq_dec Expr.tvar_val_sdec Expr.Eq Expr.liftExpr
        app map nth_error value error fold_right
        Decidables.seq_dec 
        DepList.hlist_hd DepList.hlist_tl 
        SepExpr.FM.find SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty SepExpr.FM.fold
        Compare_dec.lt_eq_lt_dec nat_rec nat_rect Peano_dec.eq_nat_dec sumbool_rec sumbool_rect
        EquivDec.equiv_dec EquivDec.nat_eq_eqdec
        f_equal 
        bedrock_funcs bedrock_types pcT stT tvWord
        fst snd
        FuncImage PredImage TypeImage
        Env.repr Env.updateAt SEP.substV

        (* remove [stateD] *)
        stateD Expr.exprD 
        Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation Expr.lookupAs
        SEP.sheapD SEP.starred SEP.sexprD
        Expr.AllProvable
        Expr.Provable
        EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
        Logic.eq_sym eq_sym f_equal
        eq_rec_r eq_rect eq_rec
        nat_rec nat_rect
        sumbool_rec sumbool_rect
        Expr.tvarD types
        
        SEP.himp SEP.sexprD Expr.Impl 
        Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation 
        Expr.lookupAs
        tvTest
        SepExpr.SDenotation SepExpr.SDomain
        EquivDec.nat_eq_eqdec  
        tvWord SEP.sheapD SEP.sepCancel
        SepExpr.impures SepExpr.pures SepExpr.other
        SEP.star_SHeap SEP.unify_remove_all 
        SEP.multimap_join SEP.liftSHeap SEP.unify_remove SEP.starred 
        Expr.tvarD Expr.Eq
        
        SepExpr.FM.fold SepExpr.FM.find SepExpr.FM.add SepExpr.FM.empty 
        bedrock_types 
                
        Compare_dec.lt_eq_lt_dec Peano_dec.eq_nat_dec
        SepExpr.FM.map ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
        ExprUnify.exprUnify ExprUnify.fold_left_2_opt 
        fold_right value error map nth_error app                                       
        pcT stT 
        EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
        ExprUnify.get_Eq
        types
        Provers.transitivityProverRec Provers.transitivityEqProver Provers.inSameGroup
        Provers.in_seq orb
        (*Provers.eqD*) Provers.eqD_seq
        Expr.typeof comparator
      ] in H.

  Implicit Arguments evalPath [ types' ].

  Definition symeval_read_word_default types' (_ : list (expr (bedrock_types ++ types'))) (_ : expr (bedrock_types ++ types'))
    (_ : SEP.SHeap (bedrock_types ++ types') pcT stT) : option (expr (bedrock_types ++ types')) :=
    None.

  Definition symeval_write_word_default types' (_ : list (expr (bedrock_types ++ types')))
    (_ : expr (bedrock_types ++ types')) (_ : expr (bedrock_types ++ types')) (_ : SEP.SHeap (bedrock_types ++ types') pcT stT)
    : option (SEP.SHeap (bedrock_types ++ types') pcT stT) :=
    None.

  Definition Correctness_default : Correctness symeval_read_word_default symeval_write_word_default.
  refine (
    {| TypeImage := nil
     ; FuncImage := fun _ => nil
     ; PredImage := fun _ => nil
     |}); 
  abstract (unfold symeval_read_word_default, symeval_write_word_default; intros; try congruence).
  Defined.
  
  Ltac default_unfolder H := cbv delta [ Correctness_default ] in H; sym_evaluator H.

  Goal forall cs stn st st' SF,
    PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) ->
    Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
    evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' ->
    Regs st' Rp = natToW 0.
  Proof.
    intros.
    sym_eval ltac:(isConst) idtac default_unfolder Correctness_default tt tt tt.
    congruence.
  Qed.

End BedrockEvaluator.
