(** This file implements symbolic evaluation for the
 ** language defined in IL.v
 **)
Require Import IL SepIL.
Require Import Word Memory.
Require Import DepList EqdepClass.
Require Import PropX.
Require Expr SepExpr.
Require Import Provers.
Require Import Env.
Import List.

Require Structured SymEval.

Set Implicit Arguments.
Set Strict Implicit.

Definition bedrock_types_r : Repr Expr.type :=
{| footprint := (
   (0, {| Expr.Impl := W 
        ; Expr.Eq := fun x y => 
          match weq x y with
            | left pf => Some pf 
            | _ => None 
          end
        |}) ::
   (1, {| Expr.Impl := settings * state
        ; Expr.Eq := fun _ _ => None
        |}) ::
   (2, {| Expr.Impl := state
        ; Expr.Eq := fun _ _ => None
        |}) ::
   (3, {| Expr.Impl := IL.test
        ; Expr.Eq := fun l r => 
          match l as l , r as r with
            | IL.Eq , IL.Eq => Some (refl_equal _)
            | IL.Ne , IL.Ne => Some (refl_equal _)
            | IL.Le , IL.Le => Some (refl_equal _)
            | IL.Lt , IL.Lt => Some (refl_equal _)
            | _ , _ => None
          end
        |}) ::
   (4, {| Expr.Impl := IL.reg
        ; Expr.Eq := fun l r =>
          match l as l , r as r with
            | IL.Sp , IL.Sp => Some (refl_equal _)
            | IL.Rp , IL.Rp => Some (refl_equal _)
            | IL.Rv , IL.Rv => Some (refl_equal _)
            | _ , _ => None
          end
        |}) :: nil) :: nil
 ; default := Expr.EmptySet_type
 |}.

Definition bedrock_types : list Expr.type :=
  Eval cbv beta iota zeta delta 
    [ repr repr' fold_right default footprint bedrock_types_r updateAt
      hd hd_error value error tl
    ]
    in repr bedrock_types_r nil.

(** Symbolic Evaluation **)
Module PLUGIN := SymEval.EvaluatorPlugin BedrockHeap ST.

Module BedrockEvaluator.
  Require Import SepExpr SymEval.
  Require Import Expr.

  Module SEP := PLUGIN.SEP.


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
    (** NOTE : I can use something like this to generate intermediate states
    | SymCheckPoint : expr types -> sym_assert.
    **)

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

  Section typed_ext.
    Variable types' : list type.
    Definition types := repr bedrock_types_r types'.

    Local Notation "'pcT'" := (tvType 0).
    Local Notation "'tvWord'" := (tvType 0).
    Local Notation "'stT'" := (tvType 1).
    Local Notation "'tvState'" := (tvType 2).
    Local Notation "'tvTest'" := (tvType 3).
    Local Notation "'tvReg'" := (tvType 4).

    Definition bedrock_funcs_r : Repr (signature (repr bedrock_types_r types')).
    refine (
      {| default := Default_signature _
        ; footprint := (
          (0, {| Domain := tvWord :: tvWord :: nil
            ; Range := tvWord
            ; Denotation := _ |}) ::
          (1, {| Domain := tvWord :: tvWord :: nil
            ; Range := tvWord
            ; Denotation := _ |}) ::
          (2, {| Domain := tvWord :: tvWord :: nil
            ; Range := tvWord
            ; Denotation := _ |}) ::
          (3, {| Domain := tvTest :: tvWord :: tvWord :: nil
            ; Range := tvProp
            ; Denotation := _ |}) :: 
          (4, {| Domain := tvState :: tvReg :: nil
            ; Range := tvWord
            ; Denotation := _ |}) :: nil) :: nil
      |});
    cbv beta iota zeta delta [ functionTypeD map ]; (repeat rewrite tvarD_repr_repr_get); simpl.
    refine (@wplus 32).
    refine (@wminus 32).
    refine (@wmult 32).
    refine comparator.
    refine Regs.
    Defined.

    Definition bedrock_funcs : functions (repr bedrock_types_r types') :=
      Eval cbv beta iota zeta delta 
        [ repr repr' default footprint fold_right bedrock_funcs_r updateAt hd_error error value
          bedrock_types_r Default_signature tl hd ]
        in repr bedrock_funcs_r nil.

    Variable funcs' : functions types.
    Definition funcs := repr bedrock_funcs_r funcs'.

    Definition fPlus (l r : expr types) : expr types :=
      Expr.Func 0 (l :: r :: nil).
    Definition fMinus (l r : expr types) : expr types :=
      Expr.Func 1 (l :: r :: nil).
    Definition fMult (l r : expr types) : expr types :=
      Expr.Func 2 (l :: r :: nil).

    Theorem fPlus_correct : forall l r uvars vars, 
      match exprD funcs uvars vars l (tvType 0) , exprD funcs uvars vars r (tvType 0) with
        | Some lv , Some rv =>
          exprD funcs uvars vars (fPlus l r) (tvType 0) = Some (wplus lv rv)
        | _ , _ => True
      end.
    Proof.
      intros; simpl; unfold eq_ind_r; simpl;
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
      intros; simpl; unfold eq_ind_r; simpl;
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
      intros; simpl; unfold eq_ind_r; simpl;
      repeat match goal with
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end ] => destruct X
             end; auto.
    Qed.

    Variable Prover : ProverT types.

    (** these are the plugin functions **)
    Variable symeval_read_word : Facts Prover -> expr types -> SEP.SHeap types pcT stT 
      -> option (expr types).
    Variable symeval_write_word : Facts Prover -> expr types -> expr types -> SEP.SHeap types pcT stT 
      -> option (SEP.SHeap types pcT stT).
    
    (** This has to be connected to the type of the intermediate representation **)
    Definition sym_evalLoc (lv : sym_loc types) (ss : SymState types pcT stT) : expr types :=
      match lv with
        | SymReg r => sym_getReg r (SymRegs ss)
        | SymImm l => l
        | SymIndir r w => fPlus (sym_getReg r (SymRegs ss)) w
      end.

    Section with_facts.
    Variable Facts : Facts Prover.

    Definition sym_evalLval (lv : sym_lvalue types) (val : expr types) (ss : SymState types pcT stT)
      : option (SymState types pcT stT) :=
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
              match symeval_write_word Facts l val m with
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

    Definition sym_evalRval (rv : sym_rvalue types) (ss : SymState types pcT stT) : option (expr types) :=
      match rv with
        | SymRvLval (SymLvReg r) =>
          Some (sym_getReg r (SymRegs ss))
        | SymRvLval (SymLvMem l) =>
          let l := sym_evalLoc l ss in
          match SymMem ss with
            | None => None
            | Some m => 
              symeval_read_word Facts l m
          end
        | SymRvImm w => Some w 
        | SymRvLabel l => None (* TODO: can we use labels? it seems like we need to reflect these as words. *)
        (* an alternative would be to reflect these as a function call that does the positioning...
         * - it isn't clear that this can be done since the environment would need to depend on the settings.
         *)
        (*Some (Expr.Const (types := types) (t := tvType 2) l) *)
      end.

    Definition sym_assertTest (r : sym_rvalue types) (t : test) (l : sym_rvalue types) (ss : SymState types pcT stT) (res : bool) 
      : option (expr types) :=
      let '(l, t, r) := if res
        then (l, t, r)
        else match t with
               | IL.Eq => (l, IL.Ne, r)
               | IL.Ne => (l, IL.Eq, r)
               | IL.Lt => (r, IL.Le, l)
               | IL.Le => (r, IL.Lt, l)
             end in
      match sym_evalRval l ss , sym_evalRval r ss with
        | Some l , Some r =>
          match t with
            | IL.Eq => Some (Expr.Equal tvWord l r)
            | _ => Some (Expr.Func 3 (Expr.Const (types := types) (t := tvTest) t :: l :: r :: nil))
          end
        | _ , _ => None
      end.

    Definition sym_evalInstr (i : sym_instr types) (ss : SymState types pcT stT) : option (SymState types pcT stT) :=
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

    Fixpoint sym_evalInstrs (is : list (sym_instr types)) (ss : SymState types pcT stT) 
      : SymState types pcT stT + (SymState types pcT stT * list (sym_instr types)) :=
      match is with
        | nil => inl ss
        | i :: is =>
          match sym_evalInstr i ss with
            | None => inr (ss, i :: is)
            | Some ss => sym_evalInstrs is ss
          end
      end.

    End with_facts.

    Definition istream : Type := list ((list (sym_instr types) * option state) + sym_assert types).

    (** TODO: I need variables here in order to call the unfolder **)
    Variable learnHook : forall P : ProverT types, SymState types pcT stT -> Facts P -> SymState types pcT stT.

    Fixpoint sym_evalStream (is : istream) (F : Facts Prover) (ss : SymState types pcT stT) 
      : option (SymState types pcT stT) + (SymState types pcT stT * istream) :=
      match is with
        | nil => inl (Some ss)
        | inl (ins, st) :: is =>
          match sym_evalInstrs F ins ss with
            | inr (ss,rm) => inr (ss, inl (rm, st) :: is)
            | inl ss => sym_evalStream is F ss
          end
        | inr asrt :: is =>
          match asrt with
            | SymAssertCond l t r (Some res) =>
              match sym_assertTest F l t r ss res with
                | Some sp =>
                  let F' := Learn Prover F (sp :: nil) in 
                  let ss' := 
                    {| SymVars := SymVars ss
                     ; SymUVars := SymUVars ss
                     ; SymRegs := SymRegs ss 
                     ; SymMem := SymMem ss
                     ; SymPures := sp :: SymPures ss
                     |}
                  in
                  let ss' := learnHook Prover ss' F' in
(*
                  let facts' := Learn Prover (SymFacts ss) (sp :: nil) in
                  (** TODO: perform unfolding here **)
                  match learnHook 
                  let mem' := SymMem ss in
                  
                  let ss' :=
                    {| SumSymRegs := SymRegs ss 
                     ; SymMem := mem' 
                     ; SymPures := sp :: SymPures ss
                     ; SymFacts := facts' 
                     |}
                  in
*)
                  sym_evalStream is F' ss'
                | None => inr (ss, inr asrt :: is)
              end
            | SymAssertCond l t r None =>
              match sym_evalRval F l ss , sym_evalRval F r ss with
                | None , _ => inl None
                | _ , None => inl None
                | _ , _ => sym_evalStream is F ss 
              end
          end
      end.

    (* Denotation functions *)
    Section sym_denote.
      Variable funcs : functions types.
      Variable uvars vars : env types.

      Definition sym_regsD (rs : SymRegType types) : option regs :=
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

    Fixpoint istreamD (is : istream) (stn : settings) (st : state) (res : option state) : Prop :=
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

      Variable sfuncs : SEP.sfunctions types pcT stT.

      Definition stateD cs (stn : IL.settings) (s : state) (ss : SymState types pcT stT) : Prop :=
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
            /\ match m with 
                 | None => True
                 | Some m => 
                   PropX.interp cs (SepIL.SepFormula.sepFormula (SEP.sexprD funcs sfuncs uvars vars (SEP.sheapD m)) (stn, s))%PropX
               end
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
    End sym_denote.
  End typed_ext.

  Section evaluator.
    Record SymEvaluator types (pcT stT : tvar) : Type :=
    { symeval_read_word : forall (P : Provers.ProverT types), Provers.Facts P -> 
      expr types -> SEP.SHeap types pcT stT -> option (expr types)
    ; symeval_write_word : forall (P : Provers.ProverT types), Provers.Facts P ->
      expr types -> expr types -> SEP.SHeap types pcT stT -> option (SEP.SHeap types pcT stT)
    }.

    Local Notation "'pcT'" := (tvType 0).
    Local Notation "'tvWord'" := (tvType 0).
    Local Notation "'stT'" := (tvType 1).
    Local Notation "'tvState'" := (tvType 2).
    Local Notation "'tvTest'" := (tvType 3).
    Local Notation "'tvReg'" := (tvType 4).

    Record SymEvaluator_correct types'
      (funcs : functions (repr bedrock_types_r types')) (preds : SEP.sfunctions (repr bedrock_types_r types') pcT stT) 
      (Evaluator : SymEvaluator (repr bedrock_types_r types') (tvType 0) (tvType 1))
      : Type :=
    { ReadCorrect :
      forall (P : Provers.ProverT (repr bedrock_types_r types')) (PE : Provers.ProverT_correct P funcs),
        forall facts (pe ve : expr (repr bedrock_types_r types')) SH,
          symeval_read_word Evaluator P facts pe SH = Some ve ->
          forall uvars vars cs p m stn,
            Provers.Valid PE uvars vars facts ->
            exprD funcs uvars vars pe tvWord = Some p ->
            PropX.interp cs (![ SEP.sexprD funcs preds uvars vars (SEP.sheapD SH) ] (stn, m)) ->
            match exprD funcs uvars vars ve tvWord with
              | Some v =>
                ReadWord stn (Mem m) p = Some v
              | _ => False
            end
    ; WriteCorrect :
      forall (P : Provers.ProverT (repr bedrock_types_r types')) (PE : Provers.ProverT_correct P funcs),
        forall uvars vars cs facts pe ve m stn SH SH',
          symeval_write_word Evaluator P facts pe ve SH = Some SH' ->
            Provers.Valid PE uvars vars facts ->
            forall p v,
            exprD funcs uvars vars pe tvWord = Some p ->
            exprD funcs uvars vars ve tvWord = Some v ->
            PropX.interp cs (![ SEP.sexprD funcs preds uvars vars (SEP.sheapD SH) ] (stn, m)) ->
            match mem_set_word _ _ (footprint_w) (BedrockHeap.mem_set) (explode stn) p v (Mem m) with
              | None => False
              | Some m' =>
                PropX.interp cs (![ SEP.sexprD funcs preds uvars vars (SEP.sheapD SH') ] (stn, {| Regs := Regs m ; Mem := m' |}))
            end
    }.

    Definition LearnHook types : Type := 
      forall P : Provers.ProverT types, SymState types pcT stT -> Provers.Facts P -> SymState types pcT stT.

    Record LearnHook_correct types' (L : LearnHook (types types')) funcs preds : Prop :=
    { hook_sound : forall P (PC : ProverT_correct P funcs),
      forall uvars vars cs stn st ss ss' pp,
      @stateD _ funcs uvars vars preds cs stn st ss ->
      Valid PC uvars vars pp ->
      L P ss pp = ss' ->
      @stateD _ funcs uvars vars preds cs stn st ss'
    }.

    Theorem sym_eval_any : forall types',
      let types := repr bedrock_types_r types' in
      forall (funcs : functions types) (sfuncs : SEP.sfunctions types _ _),
      forall E,  @SymEvaluator_correct types' funcs sfuncs E ->
      forall P, Provers.ProverT_correct P funcs ->
      forall L, @LearnHook_correct _ L funcs sfuncs ->
      forall stn uvars vars sound_or_safe st p,
        istreamD funcs uvars vars p stn st sound_or_safe ->
        forall cs ss,
        stateD funcs uvars vars sfuncs cs stn st ss ->
        let facts := Summarize P (match SymMem ss with
                                    | None => SymPures ss
                                    | Some m => pures m
                                  end) in
        let res := @sym_evalStream _ P (symeval_read_word E P) (symeval_write_word E P) L p facts ss in
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

    Theorem stateD_proof_no_heap types' : 
      let types :=  repr bedrock_types_r types' in
        forall (funcs : Expr.functions types) (P : ProverT types)
          (PC : ProverT_correct P funcs),
          forall (uvars vars : Expr.env types)
            (sfuncs : SEP.sfunctions types pcT stT) 
            (st : state) (sp rv rp : Expr.expr types),
            exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
            exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
            exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
            forall pures : list (Expr.expr types),
              Expr.AllProvable funcs uvars vars pures ->
              forall (cs : codeSpec W (settings * state)) (stn : settings),
                stateD funcs uvars vars sfuncs cs stn st
                {| SymVars := map (@projT1 _ _) vars
                  ; SymUVars := map (@projT1 _ _) uvars
                  ; SymMem := None
                  ; SymRegs := (sp, rp, rv)
                  ; SymPures := pures
                |}.
    Proof.
      unfold stateD. intros.
      unfold types.
      repeat match goal with
               | [ H : _ = _ |- _ ] => rewrite H
             end.
      intuition auto. 
    Qed.

    Theorem stateD_proof types' : 
      let types :=  repr bedrock_types_r types' in
        forall (funcs : Expr.functions types) (P : ProverT types)
          (PC : ProverT_correct P funcs),
          forall (uvars vars : Expr.env types)
            (sfuncs : SEP.sfunctions types pcT stT) 
            (st : state) (sp rv rp : Expr.expr types),
            exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
            exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
            exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
            forall pures : list (Expr.expr types),
              Expr.AllProvable funcs uvars vars pures ->
              forall (sh : SEP.sexpr types pcT stT)
                (hashed : SEP.SHeap types pcT stT),
                SEP.hash sh = (nil, hashed) ->
                forall (cs : codeSpec W (settings * state)) (stn : settings),
                  interp cs (![SEP.sexprD funcs sfuncs uvars vars sh] (stn, st)) ->
                  stateD funcs uvars vars sfuncs cs stn st
                  {| SymVars := map (@projT1 _ _) vars
                   ; SymUVars := map (@projT1 _ _) uvars
                   ; SymMem := Some hashed
                   ; SymRegs := (sp, rp, rv)
                   ; SymPures := pures
                   |}.
    Proof.
      unfold stateD. intros.
      unfold types.
      repeat match goal with
               | [ H : _ = _ |- _ ] => rewrite H
             end.
      intuition auto.
      eapply hash_interp; eauto.
    Qed.
  End evaluator.

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

        Expr.AllProvable Expr.Provable Expr.tvarD types comparator
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
        let f := constr:(nil : functions typesV) in
        build_path typesV i st v v f ltac:(fun uvars funcs is sf pf =>
          assert (@istreamD typesV funcs uvars v is stn st sf) by (exact pf))
    end.
  Abort.

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
      | tt =>
        idtac "couldn't find anything to symbolically evaluate!" 
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
                            | (?X, ?Y) => subst X ; unfold_all Y
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
                            let pluginCV := fresh "plugin" in
                            let pluginC := plugin typesV pcT stT funcsV sfuncsV in
                            pose (pluginCV := pluginC) ;
                            let unfolderC := unfolder typesV pcT stT funcsV sfuncsV in
                            let unfolderCV := fresh "unfolder" in
                            pose (unfolderCV := unfolderC) ;
                            generalize (@stateD_proof_no_heap typesV funcsV _ proverCV
                              uvars vars sfuncsV st sp_v rv_v rp_v 
                              sp_pf rv_pf rp_pf pures proofs cs stn) ;
                            let H_stateD := fresh in
                            intro H_stateD ;
                            (apply (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                stn uvars vars fin_state st is is_pf) in H_stateD ;
                             let syms := constr:((typesV, (funcsV, (sfuncsV, (proverCV, (pluginCV, unfolderCV)))))) in
                             finish H_stateD syms) || fail 100000 "couldn't apply sym_eval_any! (SF case)"
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
                             ] *)
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
                            let pluginC := plugin typesV pcT stT funcsV sfuncsV in
                            let pluginCV := fresh "plugin" in
                            pose (pluginCV := pluginC) ;
                            let unfolderC := unfolder typesV pcT stT funcsV sfuncsV in
                            let unfolderCV := fresh "unfolder" in
                            pose (unfolderCV := unfolderC) ;
                            apply (@stateD_proof typesV funcsV _ proverCV
                              uvars vars sfuncsV _ sp_v rv_v rp_v 
                              sp_pf rv_pf rp_pf pures proofs SF _ (refl_equal _)) in H_interp ;
                            (apply (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                              stn uvars vars fin_state st is is_pf) in H_interp ;
                             let syms := constr:((typesV, (funcsV, (sfuncsV, (proverCV, (pluginCV, unfolderCV)))))) in
                             finish H_interp syms) || fail 100000 "couldn't apply sym_eval_any! (SF case)" (* ||
                            first [ 
                              generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                stn uvars vars fin_state st is is_pf) ; idtac "A" |
                              pose is_pf ; generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                stn uvars vars fin_state st is) ; idtac "B" (*|
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                  stn uvars) ; idtac "C" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV
                                  stn) ; idtac "D" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV _ unfolderCV) ; idtac "E" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV _ proverCV) ; idtac "F" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV _ pluginCV) ; idtac "G" |
                                generalize (@sym_eval_any typesV funcsV sfuncsV) ; idtac "H" *) ] *)
                            )
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

        (* remove [stateD] *)
        stateD Expr.exprD 
        Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation Expr.lookupAs
        Expr.AllProvable Expr.Provable Expr.tvarD
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
        types
(*        Provers.transitivityProverRec Provers.transitivityEqProver *) Provers.inSameGroup
        Provers.in_seq orb
        (*Provers.eqD*) Provers.eqD_seq
        Expr.typeof comparator

        fPlus fMinus fMult

        repr_combine default footprint repr' updateAt Default_signature nil_Repr EmptySet_type SEP.Default_ssignature
        bedrock_funcs_r bedrock_types_r

        Summarize Learn Prove

        symeval_read_word symeval_write_word 
      ] in H.

  Implicit Arguments istreamD [ types' ].

  Module DefaultEvaluator.
    Section with_prover.
      Variable types : list type.
      Variables pcT stT : tvar.
      Variable prover : ProverT types.
      
      Definition symeval_read_word_default (_ : Facts prover) (_ : expr types)
        (_ : SEP.SHeap types pcT stT) : option (expr types) :=
        None.

      Definition symeval_write_word_default (_ : Facts prover)
        (_ : expr types) (_ : expr types) (_ : SEP.SHeap types pcT stT)
        : option (SEP.SHeap types pcT stT) :=
        None.
    End with_prover.

    Definition SymEvaluator_default types pcT stT : SymEvaluator types pcT stT.
    constructor.
    eapply symeval_read_word_default.
    eapply symeval_write_word_default.
    Defined.
    
    Definition SymEvaluator_correct_default types' (_ _ : tvar) funcs preds :     
      @SymEvaluator_correct (repr bedrock_types_r types') funcs preds
      (SymEvaluator_default (repr bedrock_types_r types') (tvType 0) (tvType 1)).
    econstructor.
      simpl; unfold symeval_read_word_default, symeval_write_word_default; simpl; congruence.
      simpl; unfold symeval_read_word_default, symeval_write_word_default; simpl; congruence.
    Qed.

    Definition defaultLearnHook types : LearnHook types :=
      fun _ x _ => x.

    Theorem defaultLearnHook_correct types' funcs preds 
      : @LearnHook_correct types' (@defaultLearnHook (types types')) funcs preds.
    Proof.
      econstructor. unfold defaultLearnHook. intros; subst; auto.
    Qed.

    Ltac simplifier H := 
      cbv delta [ 
        SymEvaluator_default
        symeval_read_word_default symeval_write_word_default
        
        defaultLearnHook
        reflexivityProver
      ] in H; sym_evaluator H.

    Goal forall (cs : codeSpec W (settings * state)) (stn : settings) st st' SF,
      PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) -> 
      Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
      evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' -> 
      Regs st' Rp = natToW 0.
    Proof.
      intros.
      Time sym_eval ltac:(isConst) 
        ltac:(fun ts fs => constr:(@reflexivityProver_correct ts fs)) (* prover *)
        ltac:(fun ts pc st fs ps => constr:(@SymEvaluator_correct_default ts pc st fs ps)) (* memory plugin *)
        ltac:(fun ts pc st fs ps => constr:(@defaultLearnHook_correct ts fs ps)) (* unfolder *)
        simplifier tt tt tt.
      congruence.
    Qed. 
  End DefaultEvaluator.


  Module PluginEvaluator.

    Section evaluator.
      Variable types : list type.
      Variable pcT stT : tvar.
      Variable evals : list (nat * PLUGIN.MemEval types). 

      Section with_prover.
        Variable Prover : ProverT types.


        Section fold_first.
          Variables T V : Type.
          Variable F : T -> option V.

          Fixpoint fold_first (ls : list T) : option V :=
            match ls with
              | nil => None
              | t :: ls =>
                match F t with
                  | None => fold_first ls
                  | x => x
                end
            end.
        End fold_first.

        Section fold_first_update.
          Variables T : Type.
          Variable F : T -> option T.

          Fixpoint fold_first_update (ls : list T) (acc : list T) : option (list T) :=
            match ls with
              | nil => None
              | t :: ls =>
                match F t with
                  | None => fold_first_update ls (t :: acc)
                  | Some v => Some (rev acc ++ v :: ls)
                end
            end.
        End fold_first_update.

        Definition plugin_symeval_read_word (facts : Facts Prover) (p : expr types) 
          (s : SEP.SHeap types pcT stT) : option (expr types) :=
          let impures := SepExpr.impures s in
          let reader i_me :=
            let '(i,me) := i_me in
            match FM.find i impures with
              | Some argss =>
                fold_first (fun args => PLUGIN.sym_read me Prover facts args p) argss
              | None => None
            end
          in
          fold_first reader evals.

        Definition plugin_symeval_write_word (facts : Facts Prover) (p v : expr types)
          (s : SEP.SHeap types pcT stT) : option (SEP.SHeap types pcT stT) :=
          let impures := SepExpr.impures s in
          let writer i_me :=
          let '(i,me) := i_me in
            match FM.find i impures with
              | Some argss =>
                match fold_first_update (fun args => PLUGIN.sym_write me Prover facts args p v) argss nil with
                  | None => None
                  | Some argss => Some (FM.add i argss impures) (** NOTE : add = replace **)
                end
              | None => None
            end
          in
          match fold_first writer evals with
            | None => None
            | Some impures => Some {| impures := impures ; pures := SepExpr.pures s ; other := SepExpr.other s |}
          end.
      End with_prover.

      Definition Plugin_SymEvaluator : SymEvaluator types pcT stT : Type :=
      {| symeval_read_word := plugin_symeval_read_word
       ; symeval_write_word := plugin_symeval_write_word
       |}.
    End evaluator.

    Ltac unfolder H :=
      cbv delta 
        [ fold_first fold_first_update 
          FM.find FM.add 
          PLUGIN.sym_read PLUGIN.sym_write 
          PLUGIN.Build_MemEval
          plugin_symeval_read_word
          plugin_symeval_write_word
          Plugin_SymEvaluator
        ] in H;
        sym_evaluator H.

    Section correctness.
      Variable types' : list type.
      Definition types := Env.repr bedrock_types_r types'.
      Definition pcT := tvType 0.
      Definition stT := tvType 1.
      Variables tvPtr tvVal : tvar.
      Variable funcs : functions types.
      Variable sfuncs : SEP.sfunctions types pcT stT .
      Variable evals : list (nat * PLUGIN.MemEval types).

      Hypothesis smem_read : settings -> tvarD types tvPtr -> smem -> option (tvarD types tvVal).
      Hypothesis smem_write : settings -> tvarD types tvPtr -> tvarD types tvVal -> smem -> option smem.

      (** TODO: This is missing the necessary pre-condition to establish the connection between
       ** [evals] and [sfuncs]
       **)
      Hypothesis sfuncs_evals : hlist (fun (i_me : nat * PLUGIN.MemEval types) => 
        let (i,me) := i_me in
        match nth_error sfuncs i with
          | None => Empty_set
          | Some sig => @PLUGIN.MemEval_correct _ me stT pcT tvPtr tvVal smem_read smem_write sig funcs
        end) evals.

      Definition Plugin_SymEvaluator_correct : @SymEvaluator_correct types funcs sfuncs (Plugin_SymEvaluator pcT stT evals).
        generalize sfuncs_evals.
        admit.
      Qed.
    End correctness.
    
  End PluginEvaluator.


End BedrockEvaluator.
