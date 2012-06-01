(** This file implements the tactics for symbolic evaluation for the
 ** language defined in IL.v
 **)
Require Import IL SepIL SymIL SymILProofs.
Require Import Word Memory.
Require Import DepList EqdepClass.
Require Import PropX.
Require Import SepExpr SymEval.
Require Import Expr.
Require Import Prover.
Require Import Env TypedPackage.
Import List.
Require Folds.

Require Structured SymEval.
Require Import ILEnv.

Set Implicit Arguments.
Set Strict Implicit.

(*
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.  
Add ML Path "/usr/local/lib/coq/user-contrib/". 
Declare ML Module "Timing_plugin".
*)

(** The Symbolic Evaluation Interfaces *)
Module MEVAL := SymIL.MEVAL.

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
  Variable sfuncs : SEP.predicates TYPES pcT stT.

  Lemma skipn_length : forall T (ls : list T) n,
    length ls = n ->
    skipn n ls = nil.
  Proof.
    clear. intros; subst; induction ls; simpl; auto.
  Qed.

  Lemma skipn_app_first : forall T (ls ls' : list T) n,
    length ls = n ->
    skipn n (ls ++ ls') = ls'.
  Proof.
    clear; intros; subst; induction ls; auto.
  Qed.

  Lemma interp_ex : forall cs T (P : T -> hprop _ _ _) stn_st,
    interp cs (![SEP.ST.ex P] stn_st) ->
    exists v, interp cs (![P v] stn_st).
  Proof.
    clear. intros.
    rewrite sepFormula_eq in *. destruct stn_st. unfold sepFormula_def in *. simpl in *.
    unfold SEP.ST.ex in H. apply interp_sound in H. auto.
  Qed.

  Lemma interp_pull_existsEach : forall cs P stn_st uvars vars' vars,
    interp cs (![SEP.sexprD funcs sfuncs uvars vars (SEP.existsEach vars' P)] stn_st) ->
    exists env', map (@projT1 _ _) env' = vars' /\
      interp cs (![SEP.sexprD funcs sfuncs uvars (rev env' ++ vars) P] stn_st).
  Proof.
    clear. 
    induction vars'; simpl; intros.
    exists nil; simpl; eauto.
    
    apply interp_ex in H.
    destruct H. eapply IHvars' in H. destruct H. intuition. exists (existT (tvarD TYPES) a x :: x0).
    simpl in *. rewrite H0. intuition eauto. rewrite app_ass. simpl. auto.
  Qed.
  
  Theorem stateD_proof_no_heap :
    forall (uvars : Expr.env TYPES) (st : state) (sp rv rp : Expr.expr TYPES),
      let vars := nil in
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
    rewrite skipn_length; eauto using map_length; simpl in *.
    repeat rewrite app_nil_r in *.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end.
    intuition auto. 
  Qed.

  Theorem stateD_proof : (* vars = nil *)
    forall (uvars : Expr.env TYPES) (st : state) (sp rv rp : Expr.expr TYPES),
      let vars := nil in
      exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
      exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
      exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
      forall pures : list (Expr.expr TYPES),
        Expr.AllProvable funcs uvars vars pures ->
        forall (sh : SEP.sexpr TYPES pcT stT)
          (hashed : SH.SHeap TYPES pcT stT) vars',
          SH.hash sh = (vars', hashed) ->
          forall (cs : codeSpec W (settings * state)) (stn : settings),
            interp cs (![SEP.sexprD funcs sfuncs uvars vars sh] (stn, st)) ->
            stateD funcs' sfuncs uvars vars cs (stn, st)
            {| SymVars := map (@projT1 _ _) vars ++ rev vars'
             ; SymUVars := map (@projT1 _ _) uvars
             ; SymMem := Some hashed
             ; SymRegs := (sp, rp, rv)
             ; SymPures := pures
            |}.
  Proof.
    Opaque repr.
    clear.
    unfold stateD. intros. simpl length. simpl.
    generalize (SH.hash_denote funcs sfuncs uvars nil cs sh). rewrite H3. simpl in *.
    intro XX. rewrite XX in H4. 

    apply interp_pull_existsEach in H4. destruct H4. intuition.
    rewrite <- H5. rewrite <- map_rev. apply existsEach_projT1_env. rewrite app_nil_r in *.
    change (rev x) with (nil ++ rev x).

    repeat (erewrite exprD_weaken by eassumption).
    intuition eauto.

    apply AllProvable_app; auto.
    { revert H2. clear.
      match goal with
        | [ |- context [ @nil ?X ] ] => generalize (@nil X)
      end.
      induction pures. auto.
      simpl. unfold Provable in *. intro.
      case_eq (exprD funcs uvars l a tvProp); intros. intuition.
      erewrite exprD_weaken by eassumption; auto.
      exfalso; intuition. 
    }
    { rewrite sepFormula_eq in H6. unfold sepFormula_def in H6. simpl in H6.
      eapply SH.sheapD_pures. 
      unfold SEP.ST.satisfies. simpl in *. eauto.
    }
  Qed.

  Variable meval : MEVAL.MemEvaluator TYPES pcT stT.
  Variable meval_correct : MEVAL.MemEvaluator_correct meval funcs sfuncs tvWord tvWord 
    (@SymIL.IL_mem_satisfies types') (@SymIL.IL_ReadWord types') (@SymIL.IL_WriteWord types').

  Variable Prover : ProverT TYPES.
  Variable PC : ProverT_correct Prover funcs.

  Variable learnHook : MEVAL.LearnHook TYPES (SymIL.SymState TYPES pcT stT).
  Variable learn_correct : @MEVAL.LearnHook_correct _ _ pcT stT learnHook (@stateD _ funcs sfuncs) funcs sfuncs.

  Lemma ApplySymEval : forall uvars vars sound_or_safe path stn st,
    istreamD funcs uvars vars path stn st sound_or_safe ->
    forall cs ss,
    stateD funcs sfuncs uvars vars cs (stn,st) ss ->
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
                  stateD funcs sfuncs meta_env var_env cs (stn, st') ss'))
          end
        | inr (ss'', is') => 
          exists st'' : state, 
            Expr.forallEach (env_ext (length vars) (SymVars ss'')) (fun venv =>
              let var_env := vars ++ venv in
              Expr.existsEach (env_ext (length uvars) (SymUVars ss'')) (fun uenv' =>
                let meta_env := uvars ++ uenv' in 
                     istreamD funcs meta_env var_env is' stn st'' None
                  /\ stateD funcs sfuncs meta_env var_env cs (stn, st'') ss''))
      end.
  Proof.
    (** This is really an exact duplicate of sym_evalStream_correct, it is here 
     ** to set the order of arguments used by the tactic.
     **)
  Admitted.

End stream_correctness.

(** Reification **)

(* Reify the instructions *)
Ltac collectTypes_loc isConst l Ts :=
  match l with
    | Reg _ => Ts
    | Imm ?i => ReifyExpr.collectTypes_expr isConst i Ts
    | Indir _ ?i => ReifyExpr.collectTypes_expr isConst i Ts
  end.
Ltac reify_loc isConst l types funcs uvars vars k :=
  match l with
    | Reg ?r => 
      let res := constr:(@SymReg types r) in
        k uvars funcs res
    | Imm ?i =>
      ReifyExpr.reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        let l := constr:(@SymImm types i) in k uvars funcs l)
    | Indir ?r ?i =>
      ReifyExpr.reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
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
    | RvImm ?i => ReifyExpr.collectTypes_expr isConst i Ts
    | RvLabel _ => let l := constr:(label:Type) in Reflect.cons_uniq l Ts
  end.

Ltac reify_rvalue isConst r types funcs uvars vars k :=
  match r with
    | RvLval ?l =>
      reify_lvalue isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        let l := constr:(@SymRvLval types l) in k uvars funcs l)
    | RvImm ?i =>
      ReifyExpr.reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
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

Lemma Some_cong : forall A (x y : A),
  x = y
  -> Some x = Some y.
  congruence.
Qed.

Ltac find_reg st r :=
  match goal with
    | [ H : Regs st r = ?x |- _ ] => constr:((x, Some_cong (eq_sym H)))
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
      | (H, _) => true
      | (_, ?Hs) => find_exact H Hs
    end
  in
  let rec get_instrs st ignore :=
    match goal with
      | [ H : Structured.evalCond ?l _ ?r _ st = Some _ |- _ ] =>
        match find_exact H ignore with
          | false =>
            let ignore := constr:((H, ignore)) in
            let v := get_instrs st ignore in
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
      let types_ := ReifyExpr.extend_all_types Ts types_ in
      let typesV := fresh "types" in
      pose (typesV := types_) ;
      let v := constr:(nil : env typesV) in
      let f := eval unfold ILEnv.bedrock_funcs in (ILEnv.bedrock_funcs typesV) in
      build_path typesV i st v v f ltac:(fun uvars funcs is sf pf =>
        assert (@istreamD typesV funcs uvars v is stn st sf)  by (exact pf))
  end.
  solve [ trivial ].
Abort.

Require Unfolder.
Require Provers.
Module U := ExprUnify.UNIFIER.
Module UNF := Unfolder.Make SH U.  
Module PACKAGED := UNF.Packaged BedrockCoreEnv.
Module PACK := PACKAGED.PACK.

Module ILAlgoTypes <: AlgoTypes SEP BedrockCoreEnv.

  Record AllAlgos (ts : list type) : Type :=
  { Prover : option (ProverT (repr BedrockCoreEnv.core ts))
  ; Hints : option (UNF.hintsPayload (repr BedrockCoreEnv.core ts) BedrockCoreEnv.pc BedrockCoreEnv.st)
  ; MemEval : option (MEVAL.MemEvaluator (repr BedrockCoreEnv.core ts) BedrockCoreEnv.pc BedrockCoreEnv.st)
  }.

Section oplus.
  Variable T : Type.
  Variable F : T -> T -> T.

  Definition oplus (l r : option T) : option T :=
    match l , r with 
      | None , _ => r
      | _ , None => l
      | Some l , Some r => Some (F l r)
    end.
End oplus.

Definition AllAlgos_composite types (l r : AllAlgos types) : AllAlgos types :=
  match l , r with
    | {| Prover  := pl ; Hints := hl ; MemEval := ml |} , {| Prover := pr ; Hints := hr ; MemEval := mr |} =>
      {| Prover  := oplus (@composite_ProverT _) pl pr 
       ; Hints   := oplus (fun l r => {| UNF.Forward := UNF.Forward l ++ UNF.Forward r
                                       ; UNF.Backward := UNF.Backward l ++ UNF.Backward r |}) hl hr
       ; MemEval := oplus (@MEVAL.Composite.MemEvaluator_composite _ BedrockCoreEnv.pc BedrockCoreEnv.st) ml mr
       |}
  end.

(*
Fixpoint AllAlgos_composite_list types pc st (ls : list (AllAlgos types)) : AllAlgos types pc st :=
  match ls with
    | nil => {| Prover := None ; Hints := None ; MemEval := None |}
    | l :: nil => l
    | l :: ls =>
      let r := AllAlgos_composite_list ls in
      AllAlgos_composite l r
  end.
*)

Record AllAlgos_correct
  (types : list type)
  (funcs : functions (repr BedrockCoreEnv.core types))
  (preds : SEP.predicates (repr BedrockCoreEnv.core types) BedrockCoreEnv.pc BedrockCoreEnv.st)
  (algos : AllAlgos types) : Type :=
{ Acorrect_Prover :
  match Prover algos with
    | None => True
    | Some P => ProverT_correct P funcs
  end
; Acorrect_Hints : 
  match Hints algos with
    | None => True
    | Some H => UNF.hintsSoundness funcs preds H
  end
; Acorrect_MemEval :
  match MemEval algos with
    | None => True
    | Some M => 
      @MEVAL.MemEvaluator_correct _ BedrockCoreEnv.pc BedrockCoreEnv.st M funcs preds
      (tvarD (repr BedrockCoreEnv.core types) BedrockCoreEnv.st) (tvType 0) (tvType 0) 
      (@IL_mem_satisfies types) (@IL_ReadWord types) (@IL_WriteWord types)
  end
}.

Theorem AllAlgos_correct_composite types (l r : AllAlgos types) funcs preds 
  (CL : @AllAlgos_correct types funcs preds l)
  (CR : @AllAlgos_correct types funcs preds r) :
  @AllAlgos_correct types funcs preds (AllAlgos_composite l r).
Proof.
  destruct l; destruct r; destruct CL; destruct CR; simpl in *; constructor; simpl.
  destruct Prover0; destruct Prover1; simpl; auto. apply composite_ProverT_correct; auto.
  destruct Hints0; destruct Hints1; simpl; auto; destruct Acorrect_Hints0; destruct Acorrect_Hints1; constructor; simpl;
    eapply Provers.Forall_app; auto.
  destruct MemEval0; destruct MemEval1; simpl; auto. apply MEVAL.Composite.MemEvaluator_correct_composite; auto.
Qed.

(*
Theorem AllAlgos_correct_composite_list types pc st (ls : list (AllAlgos types pc st)) funcs preds sat read write 
  (C : @hlist (AllAlgos types pc st) (fun A => @AllAlgos_correct types pc st A funcs preds sat read write) ls) :
  @AllAlgos_correct types pc st (AllAlgos_composite_list ls) funcs preds sat read write.
Proof.
  induction ls.
  constructor; simpl; auto.

  remember (a :: ls) as FOO. destruct C; inversion HeqFOO; subst.
  simpl. destruct ls; auto.
  apply AllAlgos_correct_composite; auto.
Qed.
*)

Record TypedPackage : Type :=
{ Env   : PACK.TypeEnv
; Algos : forall ts, AllAlgos (PACK.applyTypes Env ts)
; Algos_correct : forall ts fs ps,
  @AllAlgos_correct (PACK.applyTypes Env ts) (PACK.applyFuncs Env _ fs) (PACK.applyPreds Env _ ps) (Algos ts)
}.

Definition EnvOf : TypedPackage -> PACK.TypeEnv := Env.

Section unfolder_learnhook.
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
               ; SymPures := SymPures st ++ SH.pures m
               |}
          end
        | None => st
      end.

  Variable funcs : functions (repr bedrock_types_r types).
  Variable preds : SEP.predicates (repr bedrock_types_r types) (tvType 0) (tvType 1).
  Hypothesis hints_correct : UNF.hintsSoundness funcs preds hints.

  Theorem unfolderLearnHook_correct 
    : @MEVAL.LearnHook_correct (repr bedrock_types_r types) _ BedrockCoreEnv.pc BedrockCoreEnv.st (@unfolder_LearnHook) 
    (@stateD _ funcs preds) funcs preds.
  Proof.
    unfold unfolder_LearnHook. econstructor.

    destruct ss; simpl.
    destruct SymMem; simpl; intros; subst; eauto.
    generalize hints_correct.
    admit.
  Qed.
  Transparent UNF.forward.
End unfolder_learnhook.

  Ltac unfolder_simplifier s1 s2 s3 H := 
    match H with
      | tt => 
        cbv delta [ s1 s2 s3
          UNF.Foralls UNF.Vars UNF.UVars UNF.Heap UNF.Hyps UNF.Lhs UNF.Rhs
          UNF.Forward UNF.forward UNF.unfoldForward
          UNF.Backward UNF.backward UNF.unfoldBackward
          UNF.findWithRest UNF.find 
          equiv_dec
          UNF.substExpr
          Unfolder.FM.add

          SH.impures SH.pures SH.other
          
          Unfolder.allb andb

          length map app
          exprSubstU
          
          Folds.fold_left_2_opt U.Subst_empty

          unfolder_LearnHook
          UNF.default_hintsPayload
          UNF.findWithRest'
        ]
      | _ => 
        cbv delta [ s1 s2 s3
          UNF.Foralls UNF.Vars UNF.UVars UNF.Heap UNF.Hyps UNF.Lhs UNF.Rhs
          UNF.Forward UNF.forward UNF.unfoldForward
          UNF.Backward UNF.backward UNF.unfoldBackward
          UNF.findWithRest UNF.find 
          equiv_dec
          UNF.substExpr
          Unfolder.FM.add

          SH.impures SH.pures SH.other
          
          Unfolder.allb andb

          length map app
          exprSubstU

          Folds.fold_left_2_opt U.Subst_empty

          unfolder_LearnHook
          UNF.default_hintsPayload
          UNF.findWithRest'
        ] in H
    end.

Section apply_stream_correctness.
  Variable types' : list type.
  Local Notation "'TYPES'" := (repr bedrock_types_r types').

  Local Notation "'pcT'" := BedrockCoreEnv.pc.
  Local Notation "'tvWord'" := (tvType 0).
  Local Notation "'stT'" := BedrockCoreEnv.st.
  Local Notation "'tvState'" := (tvType 2).
  Local Notation "'tvTest'" := (tvType 3).
  Local Notation "'tvReg'" := (tvType 4).

  Variable funcs' : functions TYPES.
  Local Notation "'funcs'" := (repr (bedrock_funcs_r types') funcs').
  Variable preds : SEP.predicates TYPES pcT stT.

  Variable algos : AllAlgos TYPES.
  Variable algos_correct : @AllAlgos_correct TYPES funcs preds algos.

  (** Unfolding may have introduced some new variables, which we quantify existentially. *)
  Fixpoint quantifyNewVars (vs : variables) (en : env TYPES) (k : env TYPES -> Prop) : Prop :=
    match vs with
      | nil => k en
      | v :: vs' => exists x, quantifyNewVars vs' (en ++ existT _ v x :: nil) k
    end.

  Theorem Apply_sym_eval : forall stn uvars vars sound_or_safe st path,
    let prover := match Prover algos with
                    | None => Provers.reflexivityProver
                    | Some p => p
                  end in
    let meval := match MemEval algos with
                   | None => MEVAL.Default.MemEvaluator_default _ _ _ 
                   | Some me => me
                 end in
    let unfolder := match Hints algos with
                      | None => @MEVAL.LearnHookDefault.LearnHook_default _ _
                      | Some h => unfolder_LearnHook h 
                    end in
    istreamD funcs uvars vars path stn st sound_or_safe ->
    forall cs ss,
      stateD funcs preds uvars vars cs (stn,st) ss ->
      let facts := Summarize prover (match SymMem ss with
                                       | None => SymPures ss
                                       | Some m => SH.pures m ++ SymPures ss
                                     end) in
      (** initial unfolding **)
      let ss := unfolder prover ss facts in
      let res := @sym_evalStream _ prover meval unfolder facts path ss in

      match sound_or_safe with
        | None =>
          (** safe **)
          match res with
            | inl None => True
            | inl (Some _) => False
            | inr (ss'', is') => 
              quantifyNewVars (skipn (length vars) ss''.(SymVars)) vars (fun vars =>                
                exists st'' : state, 
                  istreamD funcs uvars vars is' stn st'' None
                  /\ stateD funcs preds uvars vars cs (stn, st'') ss'')
            end
        | Some st' =>
          (** correct **)
          match res with
            | inl None => False                
            | inl (Some ss') => quantifyNewVars (skipn (length vars) ss'.(SymVars)) vars (fun vars =>
              stateD funcs preds uvars vars cs (stn, st') ss')
            | inr (ss'', is') => 
              quantifyNewVars (skipn (length vars) ss''.(SymVars)) vars (fun vars =>                
                exists st'' : state, 
                  istreamD funcs uvars vars is' stn st'' (Some st')
                  /\ stateD funcs preds uvars vars cs (stn, st'') ss'')
          end
        end.
  Proof.
    generalize algos_correct. admit.
(*
    intros; eapply sym_eval_any; eauto.
    Focus 3.

    unfold facts. destruct PC. simpl. eapply Summarize_correct.
    revert H0; clear.
    destruct ss; destruct SymRegs0; destruct p; simpl; clear; intuition.
    destruct SymMem0; auto.
    eapply AllProvable_app; eauto.
    
    generalize SEP.sheapD_pures. unfold ST.satisfies.
    intro XX.
    rewrite sepFormula_eq in H0. unfold sepFormula_def in *.
    simpl in *.S
    specialize (XX _ (repr (bedrock_funcs_r types') funcs) (tvType 0) (tvType 1)); eauto. 
*)
  Qed.

End apply_stream_correctness.

Module SEP_REIFY := ReifySepExpr SEP.

(** NOTE:
 ** - [isConst] is an ltac function of type [* -> bool]
 ** - [ext] is the extension. it is a value of type [TypedPackage]
 ** - [simplifier] is an ltac that takes a hypothesis names and simplifies it
 **     (this should be implmented using [cbv beta iota zeta delta [ ... ] in H])
 **     (it is recommended/necessary to call [sym_evaluator] or import its simplification)
 **)
Ltac sym_eval isConst ext simplifier :=
(*  run_timer 100 ; *)
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
  let stn_st_SF :=
    match goal with
      | [ H : interp _ (![ ?SF ] ?X) |- _ ] => 
        let SF := eval unfold empB injB injBX starB exB hvarB in SF in
        constr:((X, (SF, H)))
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
  let reduce_repr sym ls :=
    match sym with
      | tt =>
        eval cbv beta iota zeta delta [ 
          ext
          Env.repr_combine Env.listToRepr Env.listOptToRepr nil_Repr
          PACK.Types PACK.Funcs PACK.Preds Env
          PACK.applyTypes PACK.applyFuncs PACK.applyPreds
          tl map repr
          PACK.CE.core
          bedrock_types_r bedrock_funcs_r
        ] in ls
      | _ => 
        eval cbv beta iota zeta delta [
          sym ext
          Env.repr_combine Env.listToRepr Env.listOptToRepr nil_Repr
          PACK.Types PACK.Funcs PACK.Preds Env
          PACK.applyTypes PACK.applyFuncs PACK.applyPreds
          map tl repr
          PACK.CE.core
          bedrock_types_r bedrock_funcs_r
        ] in ls
    end
  in
  let ext' := 
    match ext with
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
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
(*                  stop_timer 100 ; *)
(*                  run_timer 101 ; *)
                  let all_instrs := get_instrs st in
                  let all_props := 
                    ReifyExpr.collect_props ltac:(SEP_REIFY.reflectable shouldReflect)
                  in
                  let pures := ReifyExpr.props_types all_props in
                  let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
(*                  stop_timer 101 ; *)
                  (** collect the raw types **)
(*                  run_timer 102 ; *)
                  let Ts := constr:(@nil Type) in
                  let Ts := 
                    match SF with
                      | tt => Ts
                      | (?SF,_) => (** TODO: a little sketchy since it is in CPS **)
                        SEP_REIFY.collectTypes_sexpr ltac:(isConst) SF Ts ltac:(fun Ts => Ts)
                    end
                  in
                  let Ts := collectAllTypes_instrs all_instrs Ts in
                  let Ts := Expr.ReifyExpr.collectTypes_exprs ltac:(isConst) regs Ts in
                  let Ts := Expr.ReifyExpr.collectTypes_exprs ltac:(isConst) pures Ts in
                  (** check for potential universe problems **)
                  match Ts with
                    | context [ PropX.PropX ] => 
                      fail 1000 "found PropX in types list"
                        "(this causes universe inconsistencies)" Ts
                    | context [ PropX.spec ] => 
                      fail 1000 "found PropX.spec in types list"
                        "(this causes universe inconsistencies)" Ts
                    | _ => idtac
                  end;
                  (** elaborate the types **)
                  let types_ := reduce_repr tt (PACK.applyTypes (Env ext) nil) in
                  let types_ := ReifyExpr.extend_all_types Ts types_ in
                  let typesV := fresh "types" in
                  pose (typesV := types_);
                  (** Check the types **)
                  let pcT := constr:(tvType 0) in
                  let stT := constr:(tvType 1) in
                  (** build the variables **)
                  let uvars := constr:(@nil (@sigT Expr.tvar (fun t : Expr.tvar => Expr.tvarD typesV t))) in
                  let vars := uvars in
                  (** build the base functions **)
                  let funcs := reduce_repr tt (PACK.applyFuncs (Env ext) typesV (repr (bedrock_funcs_r typesV) nil)) in
                   (** build the base sfunctions **)
(*                  let preds := constr:(@nil (@SEP.ssignature typesV pcT stT)) in *)
                  let preds := reduce_repr tt (PACK.applyPreds (Env ext) typesV nil) in
                  (** reflect the expressions **)
                  Expr.ReifyExpr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
                  let proofs := ReifyExpr.props_proof all_props in
                  Expr.ReifyExpr.reify_expr ltac:(isConst) rp_v typesV funcs uvars vars ltac:(fun uvars funcs rp_v =>
                  Expr.ReifyExpr.reify_expr ltac:(isConst) sp_v typesV funcs uvars vars ltac:(fun uvars funcs sp_v =>
                  Expr.ReifyExpr.reify_expr ltac:(isConst) rv_v typesV funcs uvars vars ltac:(fun uvars funcs rv_v =>
                    let finish H  :=
(*                      run_timer 110 ; *)
                      ((try exact H) ||
                       (let rec destruct_exs H :=
                         match type of H with
                           | Logic.ex _ =>
                             destruct H as [ ? H ] ; destruct_exs H
                           | (_ /\ (_ /\ _)) /\ (_ /\ _) =>
                             destruct H as [ [ ? [ ? ? ] ] [ ? ? ] ];
                               repeat match goal with
                                        | [ H' : _ /\ _ |- _ ] => destruct H'
                                      end
                           | ?G =>
                             fail 100000 "bad result goal" G 
                         end
                        in let fresh Hcopy := fresh "Hcopy" in
                          let T := type of H in
                            assert (Hcopy : T) by apply H; clear H; destruct_exs Hcopy))
(*                      stop_timer 110 *)
                    in
                    build_path typesV all_instrs st uvars vars funcs ltac:(fun uvars funcs is fin_state is_pf =>
                      match SF with
                        | tt => 
(*                          stop_timer 102 ; *)
                          let funcsV := fresh "funcs" in
                          pose (funcsV := funcs) ;
                          let predsV := fresh "preds" in
                          pose (predsV := preds) ;
(*                          let ExtC := constr:(@Algos_correct _ _ _ _ _ _ ext typesV funcsV predsV) in *)
                          generalize (@stateD_proof_no_heap typesV funcsV predsV
                            uvars st sp_v rv_v rp_v 
                            sp_pf rv_pf rp_pf pures proofs cs stn) ;
                          let H_stateD := fresh in
                          intro H_stateD ;
                          ((apply (@Apply_sym_eval typesV funcsV predsV
                            (@Algos ext typesV) (@Algos_correct ext typesV funcsV predsV)
                            stn uvars vars fin_state st is is_pf) in H_stateD)
                          || fail 100000 "couldn't apply sym_eval_any! (non-SF case)") ;
                          first [ simplifier typesV funcsV predsV H_stateD | fail 100000 "simplifier failed! (non-SF)" ] ;
                          try clear typesV funcsV predsV ;
                          first [ finish H_stateD | fail 100000 "finisher failed! (non-SF)" ]
                        | (?SF, ?H_interp) =>
                          SEP_REIFY.reify_sexpr ltac:(isConst) SF typesV funcs pcT stT preds uvars vars 
                          ltac:(fun uvars funcs preds SF =>
(*                            stop_timer 102 ; *)
(*                            run_timer 103 ; *)
                            let funcsV := fresh "funcs" in
                            pose (funcsV := funcs) ;
                            let predsV := fresh "preds" in
                            pose (predsV := preds) ;
(*                            let ExtC := constr:(@Algos_correct ext typesV funcsV predsV) in *)
(*                            stop_timer 103 ; *)
(*                            run_timer 104 ; *)
                            apply (@stateD_proof typesV funcsV predsV
                              uvars _ sp_v rv_v rp_v 
                              sp_pf rv_pf rp_pf pures proofs SF _ _ (refl_equal _)) in H_interp ;
(*                            stop_timer 104 ; *)
(*                            run_timer 105 ; *)
                            ((apply (@Apply_sym_eval typesV funcsV predsV
                              (@Algos ext typesV) (@Algos_correct ext typesV funcsV predsV)
                              stn uvars vars fin_state st is is_pf) in H_interp) ||
                             (idtac "couldn't apply sym_eval_any! (SF case)"; 
                               first [ 
                                 generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@Algos ext typesV) (@Algos_correct ext typesV funcsV predsV)
                                   stn uvars vars fin_state st is is_pf) ; idtac "6" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@Algos ext typesV) (@Algos_correct ext typesV funcsV predsV)
                                   stn uvars vars fin_state st) ; idtac "5"  
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@Algos ext typesV) (@Algos_correct ext typesV funcsV predsV)
                                   stn uvars vars) ; idtac "4" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@Algos ext typesV) (@Algos_correct ext typesV funcsV predsV)); idtac "3" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@Algos ext typesV)) ; generalize (@Algos_correct ext typesV funcsV predsV) ; idtac "2" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV) ; idtac "1"  
                               ])) ;
(*                             stop_timer 105 ; *)
(*                             run_timer 106 ; *)
                            first [ simplifier typesV funcsV predsV H_interp | fail 100000 "simplifier failed! (SF)" ] ;
                            try clear typesV funcsV predsV ;
                            first [ finish H_interp | fail 100000 "finisher failed! (SF)" ])
                      end)))))
              end
          end
      end
  end.

Ltac sym_evaluator sym1 sym2 sym3 H := 
  unfolder_simplifier sym1 sym2 sym3 H ;
  cbv beta iota zeta delta
    [ sym_evalInstrs sym_evalInstr sym_evalLval sym_evalRval sym_evalLoc sym_evalStream sym_assertTest
      sym_setReg sym_getReg
      SH.pures SH.impures SH.other
      SymMem SymRegs SymPures SymVars SymUVars
      SH.star_SHeap SH.liftSHeap SepHeap.MM.mmap_join 
      SepHeap.MM.mmap_mapi SepHeap.MM.mmap_map
      Expr.expr_seq_dec Expr.tvar_val_seqb Expr.Eqb Expr.liftExpr
      Expr.const_seqb
      ILEnv.bedrock_type_W
      ILEnv.bedrock_type_setting_X_state
      ILEnv.bedrock_type_setting
      ILEnv.bedrock_type_test
      ILEnv.bedrock_type_reg
      Expr.ReifyExpr.default_type

      SH.sheap_liftVars
      app map nth_error value error fold_right hd hd_error tl tail rev
      Decidables.seq_dec 
      DepList.hlist_hd DepList.hlist_tl 
      SepHeap.FM.find SepHeap.FM.add SepHeap.FM.remove SepHeap.FM.map SepHeap.FM.empty SepHeap.FM.fold
      Compare_dec.lt_eq_lt_dec nat_rec nat_rect Peano_dec.eq_nat_dec sumbool_rec sumbool_rect
      EquivDec.equiv_dec EquivDec.nat_eq_eqdec
      f_equal 
      bedrock_funcs_r bedrock_types
      fst snd
      Env.repr Env.updateAt 

      stateD existsEach Expr.exprD 
      Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation Expr.lookupAs
      Expr.AllProvable Expr.AllProvable_gen Expr.Provable Expr.tvarD
      SH.sheapD SH.starred SEP.sexprD
      EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
      Logic.eq_sym eq_sym f_equal
      eq_rec_r eq_rect eq_rec
      nat_rec nat_rect
      sumbool_rec sumbool_rect
      
      SEP.himp SEP.sexprD Expr.Impl 
      Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation 
      Expr.lookupAs
      SEP.SDenotation SEP.SDomain
      EquivDec.nat_eq_eqdec  
      SH.sheapD (* SEP.sepCancel *) (* symbolic evaluation doesn't need cancelation **)
      SH.star_SHeap (*SEP.unify_remove_all*)
      SepHeap.MM.mmap_join SH.liftSHeap SH.starred 
      Expr.tvarD 
      
      SepHeap.FM.fold SepHeap.FM.find SepHeap.FM.add SepHeap.FM.empty 
      bedrock_types 
        
      Compare_dec.lt_eq_lt_dec Peano_dec.eq_nat_dec
      SepHeap.FM.map Folds.fold_left_2_opt U.Subst_empty
      U.exprUnify
      EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
      Expr.get_Eq
      orb
        
      Expr.typeof comparator

      fPlus fMinus fMult
      
      repr_combine default footprint repr' updateAt Default_signature nil_Repr EmptySet_type SEP.Default_predicate
      bedrock_funcs_r bedrock_types_r

      Summarize Learn Prove
      
      MEVAL.smemeval_read_word MEVAL.smemeval_write_word
      
      EquivDec_nat Peano_dec.eq_nat_dec

      Prover.Prove Prover.Facts Prover.Learn Prover.Summarize

      Hints Prover MemEval Env PACK.Funcs PACK.Types PACK.Preds Algos

      (** expression unification **)
      U.exprUnify U.exprUnify_recursor
      U.subst_exprInstantiate
      U.Subst_lookup U.subst_lookup
      U.Subst_empty U.subst_empty
      U.Subst_set U.subst_set
      U.Subst_equations
      U.mentionsU
      U.dep_in 
      U.exprUnify_recursor
      
      U.FM.Raw.height U.FM.Raw.cardinal U.FM.Raw.assert_false U.FM.Raw.create
      U.FM.Raw.bal U.FM.Raw.remove_min U.FM.Raw.merge U.FM.Raw.join
      U.FM.Raw.t_left U.FM.Raw.t_opt U.FM.Raw.t_right
      U.FM.Raw.cardinal U.FM.Raw.empty U.FM.Raw.is_empty
      U.FM.Raw.mem U.FM.Raw.find   
      U.FM.Raw.add  U.FM.Raw.remove
      U.FM.Raw.fold U.FM.Raw.map U.FM.Raw.mapi U.FM.Raw.map2
        
      U.FM.this U.FM.is_bst
      U.FM.empty U.FM.is_empty
      U.FM.add U.FM.remove
      U.FM.mem U.FM.find
      U.FM.map U.FM.mapi U.FM.map2
      U.FM.elements U.FM.cardinal U.FM.fold
      U.FM.equal

      Compare_dec.lt_dec
      Compare_dec.le_dec
      Compare_dec.le_gt_dec
      Compare_dec.le_lt_dec
      Compare_dec.lt_eq_lt_dec

      U.Subst_lookup U.subst_lookup
      U.exprInstantiate U.subst_exprInstantiate

      (*ExprUnify.Subst_replace ExprUnify.env_of_Subst
      ExprUnify.get_Eq ExprUnify.exprUnifyArgs ExprUnify.exprUnify
      ExprUnify.empty_Subst
      *)

      SepHeap.MM.mmap_add SepHeap.MM.empty SepHeap.FM.find
      SepHeap.FM.Raw.find
      SepHeap.FM.this SepHeap.FM.empty SepHeap.FM.Raw.empty

(*
      ExprUnify.SUBST.empty
      ExprUnify.SUBST.find
      ExprUnify.SUBST.add
      ExprUnify.SUBST.insert_at_right
      ExprUnify.SUBST.remove
      ExprUnify.SUBST.remove_add
      ExprUnify.SUBST.find_add
      ExprUnify.SUBST.fold
      ExprUnify.SUBST.map
*)

      NatMap.Ordered_nat.compare
      NatMap.Ordered_nat.eq_dec
      Peano_dec.eq_nat_dec

      Folds.fold_left_3_opt
      sumor_rec sumor_rect

      (** unfolder should be unnecessary... **)
      UNF.Vars UNF.UVars UNF.Heap 
      UNF.Foralls UNF.Hyps UNF.Lhs UNF.Rhs 
      UNF.Forward UNF.Backward 
      UNF.forward UNF.unfoldForward UNF.findWithRest UNF.find
      equiv_dec UNF.substExpr Unfolder.FM.add 
      Unfolder.allb andb length map app exprSubstU
      unfolder_LearnHook
      UNF.default_hintsPayload UNF.findWithRest'
      UNF.findWithRest

      SH.hash SH.star_SHeap SH.liftSHeap SepHeap.MM.mmap_join map UNF.substExpr
      rev_append

      Unfolder.FM.fold Unfolder.FM.add

(*
      Unfolder.FM.empty
      Unfolder.FM.find
      Unfolder.FM.add
      Unfolder.FM.insert_at_right
      Unfolder.FM.remove
      Unfolder.FM.remove_add
      Unfolder.FM.find_add
      Unfolder.FM.fold
      Unfolder.FM.map
*)

      (** NatMap **)
      NatMap.singleton
      NatMap.IntMap.Raw.height NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.assert_false NatMap.IntMap.Raw.create
      NatMap.IntMap.Raw.bal NatMap.IntMap.Raw.remove_min NatMap.IntMap.Raw.merge NatMap.IntMap.Raw.join
      NatMap.IntMap.Raw.t_left NatMap.IntMap.Raw.t_opt NatMap.IntMap.Raw.t_right
      NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.empty NatMap.IntMap.Raw.is_empty
      NatMap.IntMap.Raw.mem NatMap.IntMap.Raw.find   
      NatMap.IntMap.Raw.add  NatMap.IntMap.Raw.remove
      NatMap.IntMap.Raw.fold NatMap.IntMap.Raw.map NatMap.IntMap.Raw.mapi NatMap.IntMap.Raw.map2

      NatMap.IntMap.this NatMap.IntMap.is_bst
      NatMap.IntMap.empty NatMap.IntMap.is_empty
      NatMap.IntMap.add NatMap.IntMap.remove
      NatMap.IntMap.mem NatMap.IntMap.find
      NatMap.IntMap.map NatMap.IntMap.mapi NatMap.IntMap.map2
      NatMap.IntMap.elements NatMap.IntMap.cardinal NatMap.IntMap.fold
      NatMap.IntMap.equal

      Int.Z_as_Int._0 Int.Z_as_Int._1 Int.Z_as_Int._2 Int.Z_as_Int._3
      Int.Z_as_Int.plus Int.Z_as_Int.max
      Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec

      ZArith_dec.Z_gt_le_dec ZArith_dec.Z_ge_lt_dec ZArith_dec.Z_ge_dec
      ZArith_dec.Z_gt_dec 
      ZArith_dec.Zcompare_rec ZArith_dec.Zcompare_rect

      BinInt.Z.add BinInt.Z.max BinInt.Z.pos_sub
      BinInt.Z.double BinInt.Z.succ_double BinInt.Z.pred_double
      
      BinInt.Z.compare

      BinPos.Pos.add BinPos.Pos.compare 
      BinPos.Pos.succ BinPos.Pos.compare_cont

      Compare_dec.nat_compare CompOpp 

      NatMap.Ordered_nat.compare

      sumor_rec sumor_rect
      sumbool_rec sumbool_rect
      eq_ind_r 


      plus minus skipn quantifyNewVars Expr.Impl_ projT1 projT2
    ] in H.

Module EmptyPackage.
  Definition empty_package : TypedPackage.
  refine (
    {| Env := {| PACK.Types := nil_Repr EmptySet_type
               ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
               ; PACK.Preds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
               |} 
     ; Algos := fun ts => {| Prover := None ; Hints := None ; MemEval := None |}
     ; Algos_correct := _
     |}).
  abstract (constructor; simpl; trivial).
  Defined.
  

  Ltac simplifier s1 s2 s3 H :=
    match H with
      | tt => 
        cbv delta [ s1 s2 s3
          empty_package UNF.default_hintsPayload
        ]
      | _ => 
        cbv delta [ s1 s2 s3
          empty_package UNF.default_hintsPayload
        ] in H
    end ;
    MEVAL.LearnHookDefault.unfolder H ;
    Provers.unfold_reflexivityProver H ;
    MEVAL.Default.unfolder H ;
    sym_evaluator s1 s2 s3 H.

  Goal forall (cs : codeSpec W (settings * state)) (stn : settings) st st' SF,
    PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) -> 
    Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
    evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' ->
    Regs st' Rp = natToW 0.
  Proof.
   intros.
   sym_eval ltac:(isConst) empty_package simplifier.
   intuition congruence. 
  Abort.

End EmptyPackage.

Module BedrockPackage.
  Definition bedrock_package : TypedPackage.
  refine (
    {| Env := {| PACK.Types := nil_Repr EmptySet_type
               ; PACK.Funcs := bedrock_funcs_r 
               ; PACK.Preds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
               |}
     ; Algos := fun ts => {| Prover := None ; Hints := None ; MemEval := None |}
     ; Algos_correct := _
     |}).
  abstract (constructor; simpl; trivial).
  Defined.

  Ltac simplifier H :=
    match H with
      | tt => 
        cbv delta [
          bedrock_package UNF.default_hintsPayload
        ]
      | _ => 
        cbv delta [
          bedrock_package UNF.default_hintsPayload
        ] in H
    end ;
    MEVAL.LearnHookDefault.unfolder H ;
    Provers.unfold_reflexivityProver H ;
    MEVAL.Default.unfolder H ;
    sym_evaluator H.
End BedrockPackage.

Module Package.

Ltac build_prover_pack prover ret :=
  let res := constr:( 
    let env :=
      {| PACK.Types := Prover.ProverTypes prover
       ; PACK.Funcs := fun ts => 
         nil_Repr (Default_signature (repr bedrock_types_r (repr (Prover.ProverTypes prover) ts)))
       ; PACK.Preds := fun ts =>
         nil_Repr (SEP.Default_predicate (repr bedrock_types_r (repr (Prover.ProverTypes prover) ts)) (tvType 0) (tvType 1))
       |} 
    in
    let algos ts :=
      @Build_AllAlgos (PACK.applyTypes env ts)
         (Some (Prover.Prover prover (PACK.applyTypes env ts)))
         None
         None
    in
    {| Env := env
     ; Algos := algos
     ; Algos_correct := fun ts fs ps =>
       let types := repr bedrock_types_r (repr (Prover.ProverTypes prover) ts) in
       @Build_AllAlgos_correct types fs ps (algos ts)
         (@Prover.Prover_correct prover types fs)
         I I
     |})
  in
  let res := eval simpl in res in
  ret res.

Goal TypedPackage.
  build_prover_pack Provers.TransitivityProver ltac:(fun x => refine x).
Defined.

Ltac build_mem_pack mem ret :=
  match type of mem with
    | @MEVAL.MemEvaluatorPackage ?tr ?pc ?st ?ptr ?val IL_mem_satisfies IL_ReadWord IL_WriteWord =>
      (let res := constr:(
        let TR := Env.repr_combine tr (MEVAL.MemEvalTypes mem) in
        let env := 
          {| PACK.Types := TR
           ; PACK.Funcs := fun ts => MEVAL.MemEvalFuncs mem (Env.repr ILEnv.bedrock_types_r (Env.repr TR ts))
           ; PACK.Preds := fun ts => MEVAL.MemEvalPreds mem (Env.repr ILEnv.bedrock_types_r (Env.repr TR ts))
           |}
        in
        let algos ts :=
          @Build_AllAlgos (PACK.applyTypes env ts) 
             None
             None 
             (Some (MEVAL.MemEval mem (PACK.applyTypes env ts)))
        in
        @Build_TypedPackage env algos 
          (fun ts fs ps => @Build_AllAlgos_correct _ _ _ (algos ts) I I
            (MEVAL.MemEval_correct mem (Env.repr ILEnv.bedrock_types_r ts) _ _))) in
      let res := eval simpl in res in
      ret res) || fail 10000 "couldn't construct mem_package"
    | ?T => 
      fail 10000 "got bad type" T "expected value of type Packages.MemEvaluatorPackage"
  end.

Definition min_types_r : Repr type :=
  {| footprint := firstn 2 (footprint bedrock_types_r)
   ; default := default bedrock_types_r
   |}.

Goal TypedPackage.
  pose (mem := 
    {| MEVAL.MemEvalTypes := nil_Repr EmptySet_type
     ; MEVAL.MemEvalFuncs := fun ts => nil_Repr (Default_signature _)
     ; MEVAL.MemEvalPreds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
     ; MEVAL.MemEval := fun ts => @MEVAL.Default.MemEvaluator_default _ (tvType 0) (tvType 1)
     ; MEVAL.MemEval_correct := fun ts fs ps =>
       @MEVAL.Default.MemEvaluator_default_correct _ _ _ _ _ _ _ _ _ _ _
     |} : @MEVAL.MemEvaluatorPackage min_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) IL_mem_satisfies IL_ReadWord IL_WriteWord).
  build_mem_pack mem ltac:(fun x => refine x).
Defined.

(** builds a [TypedPackage] from the arguments
 ** - [hints] is a list of separation logic hints
 ** - [prover] is instance of [ProverT_correct]
 ** - [mem] is a tuple of [forall ts fs ps, MemEvaluator_correct ts fs ps] plugin correct instances
 **)
Ltac build_hints_pack hints ret :=
  let res := constr:(
    let env :=
      {| PACK.Types := PACKAGED.Types hints
       ; PACK.Funcs := fun ts => PACKAGED.Functions hints (repr bedrock_types_r ts)
       ; PACK.Preds := fun ts => PACKAGED.Predicates hints (repr bedrock_types_r ts) |}
    in
    let algos ts := 
      @Build_AllAlgos (PACK.applyTypes env ts)
        None 
        (Some (PACKAGED.Hints hints ts))
        None
    in
    @Build_TypedPackage env algos 
     (fun ts fs ps => 
       let types := repr bedrock_types_r (repr (PACKAGED.Types hints) ts) in
       @Build_AllAlgos_correct _ _ _ (algos ts)
         I (PACKAGED.HintsOk hints ts fs ps) I))
  in
  let res := eval simpl in res in
  ret res.

Definition bedrock_env : PACK.TypeEnv :=
  {| PACK.Types := nil_Repr EmptySet_type
   ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
   ; PACK.Preds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
  |}.

Goal TypedPackage.
  PACKAGED.prepareHints ltac:(fun x => x) W (prod IL.settings IL.state) ltac:(isConst) bedrock_env tt tt ltac:(fun v => 
    build_hints_pack v ltac:(fun x => refine x)).
Defined.


(** given to [TypedPackage]s, combines them and passes the combined [TypedPackage]
 ** to [k].
 ** This tactic will fail if any of the environments are not compatible.
 **)
Ltac glue_pack left_pack right_pack ret :=
  let res := constr:(
    let l := left_pack in
    let r := right_pack in
    let ntypesV := Env.repr_combine (PACK.Types (Env l)) (PACK.Types (Env r)) in
    let nfuncsV ts := 
      Env.repr_combine (PACK.Funcs (Env l) (Env.repr ntypesV ts)) 
                       (PACK.Funcs (Env r) (Env.repr ntypesV ts))
    in
    let npredsV ts :=
      Env.repr_combine (PACK.Preds (Env l) (Env.repr ntypesV ts))
                       (PACK.Preds (Env r) (Env.repr ntypesV ts))
    in
    let env :=
      {| PACK.Types := ntypesV
       ; PACK.Funcs := nfuncsV
       ; PACK.Preds := npredsV
       |}
    in
    let algos ts := 
      AllAlgos_composite (Algos l (Env.repr ntypesV ts)) (Algos r (Env.repr ntypesV ts))
    in
    {| Env   := env 
     ; Algos := algos 
     ; Algos_correct := fun ts fs ps =>
       AllAlgos_correct_composite (@Algos_correct l (Env.repr ntypesV ts)
                                                    (Env.repr (nfuncsV ts) fs)
                                                    (Env.repr (npredsV ts) ps))
                                  (@Algos_correct r (Env.repr ntypesV ts)
                                                    (Env.repr (nfuncsV ts) fs)
                                                    (Env.repr (npredsV ts) ps))
    |})
  in ret res.

(*
Ltac refine_glue_pack l r :=
  let reduce_repr e := e in
  let opaque v k := k v in
  match eval hnf in l with
    | @Build_TypedPackage ?CT ?PC ?ST ?SAT ?READ ?WRITE ?tl ?fl ?pl ?al ?acl =>
      match eval hnf in r with
        | @Build_TypedPackage _ _ _ _ _ _ ?tr ?fr ?pr ?ar ?acr =>
          refine (
              let types := repr_combine tl tr in
              let funcs := fun ts => repr_combine (fl (repr types ts)) (fr (repr types ts)) in
              let preds := fun ts => repr_combine (pl (repr types ts)) (pr (repr types ts)) in
              @Build_TypedPackage CT PC ST SAT READ WRITE 
                types funcs preds
                (fun ts => AllAlgos_composite (al (repr types ts)) (ar (repr types ts)))
                _ 
               ); 
          (subst; abstract exact (fun ts fs ps => AllAlgos_correct_composite 
                  (acl (repr (repr_combine tl tr) ts) 
                       (repr (repr_combine (fl (repr (repr_combine tl tr) ts)) (fr (repr (repr_combine tl tr) ts))) fs)
                       (repr (repr_combine (pl (repr (repr_combine tl tr) ts)) (pr (repr (repr_combine tl tr) ts))) ps))
                  (acr (repr (repr_combine tl tr) ts)
                       (repr (repr_combine (fl (repr (repr_combine tl tr) ts)) (fr (repr (repr_combine tl tr) ts))) fs)
                       (repr (repr_combine (pl (repr (repr_combine tl tr) ts)) (pr (repr (repr_combine tl tr) ts))) ps))))
      end
  end.

Ltac hlist_from_tuple tpl acc := 
  match tpl with
    | tt => acc
    | (?L, ?R) => 
      let acc := hlist_from_tuple R acc in
      hlist_from_tuple L acc
    | _ => constr:(@HCons _ _ _ _ tpl acc)
  end.
*)

(** given a tuple or list of [TypedPackage]s, this tactic combines them all and calls [k] with 
 ** the result.
 **)
Ltac glue_packs packs k :=
  match type of packs with
    | TypedPackage => k packs
    | _ =>
      match packs with
        | tt => k BedrockPackage.bedrock_package
        | nil => k BedrockPackage.bedrock_package
        | ?L :: ?R =>
          glue_packs R ltac:(fun R => glue_pack L)
        | (?L, ?R) =>
          glue_packs L ltac:(fun L => 
          glue_packs R ltac:(fun R => 
            glue_pack L R k))
      end
  end.

(** TODO: is there a way to make this more efficient? **)
Ltac opaque_pack pack :=
  let pack := eval hnf in pack in
  let pack := eval simpl in pack in
  match pack with
    | @Build_TypedPackage ?env ?algos ?pf =>
      refine (@Build_TypedPackage env algos _); abstract (exact pf)
  end.

Goal TypedPackage.
  build_prover_pack Provers.TransitivityProver ltac:(fun x => 
    build_mem_pack (MEVAL.Default.package bedrock_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) IL_mem_satisfies IL_ReadWord IL_WriteWord) ltac:(fun y =>   
    glue_pack x y ltac:(opaque_pack))).
Qed.

(*
Goal TypedPackage bedrock_types_r (tvType 0) (tvType 1) IL_mem_satisfies IL_ReadWord IL_WriteWord.
  build_prover_pack Provers.TransitivityProver ltac:(fun x => 
    build_mem_pack (MEVAL.Default.package bedrock_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) IL_mem_satisfies IL_ReadWord IL_WriteWord) ltac:(fun y =>   
      idtac "1" ;
    glue_packs (x, y, y) ltac:(fun v => exact v))).
Qed.
*)
End Package.
Definition AlgoImpl := AllAlgos.
Definition AlgoProof := AllAlgos_correct.
End ILAlgoTypes.

(**
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
    Variable preds : SEP.predicates (repr bedrock_types_r types) (tvType 0) (tvType 1).
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
**)

(**
Module PluginEvaluator.
  
  Definition plugin_evaluator ts (fs : functions (repr bedrock_types_r ts)) ps evals consistent_pf := 
    @MEVAL.Plugin.PluginMemEvaluator_correct _ (tvType 0) (tvType 1) evals fs ps (settings * state) (tvType 0) (tvType 0)
    (@IL_mem_satisfies ts)
    (@IL_ReadWord ts)
    (@IL_WriteWord ts)
    consistent_pf.

  (** This Ltac builds a function that can be instantiated to build a composite evaluator.
   ** It should be applied to one argument and passed as the 3rd argument to [sym_eval].
   ** Arguments:
   ** - [known] is a tuple of [forall ts fs, @MemEvalPred_correct ts ? (tvType 0) (tvType 1) ? (tvType 0) (tvType 0) ... ]
   **)
  Ltac plugin_eval known :=
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
      let psVal := eval hnf in ps in
      let rec build_pf known k :=
        match known with
          | tt => 
            let r := constr:(@nil (nat * MEVAL.Plugin.MemEvalPred (repr bedrock_types_r ts))) in
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
          idtac "a" evals consistent_pf ;
        let res := constr:(@plugin_evaluator ts fs ps evals consistent_pf) in
          idtac "B" res;
            pose res ;
        k evalsV res).

  Goal forall ts fs ps, 
    { evals : _ & MEVAL.MemEvaluator_correct
        (MEVAL.Plugin.MemEvaluator_plugin (tvType 0) (tvType 1) evals) fs ps
        (tvType 0) (tvType 0) (@IL_mem_satisfies ts) (@IL_ReadWord ts) (@IL_WriteWord ts) }.
  Proof.
    intros.
    plugin_eval tt ts (tvType 0) (tvType 1) fs ps ltac:(fun evals pf => econstructor; apply pf).


forall (cs : codeSpec W (settings * state)) (stn : settings) st st' SF,
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
**)