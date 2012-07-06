(** This file implements the tactics for symbolic evaluation for the
 ** language defined in IL.v
 **)
Require Import IL SepIL SymIL SymILProofs.
Require Import Word Memory.
Require Import DepList EqdepClass.
Require Import PropX.
Require Import SepExpr SymEval.
Require Import Expr ReifyExpr.
Require Import Prover.
Require Import Env TypedPackage.
Import List Tactics Reflection.
Require Folds.
Require Import TacPackIL.

Require Structured SymEval.
Require Import ILEnv.

Set Implicit Arguments.
Set Strict Implicit.

(*TIME
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.  
Add ML Path "/usr/local/lib/coq/user-contrib/". 
Declare ML Module "Timing_plugin".
*)

(** The Symbolic Evaluation Interfaces *)
Module MEVAL := SymIL.MEVAL.

(** The instantiation of the learn hook with the unfolder **)
Section unfolder_learnhook.
  Variable types : list type.
  Variable hints : UNF.hintsPayload (repr bedrock_types_r types) (tvType 0) (tvType 1).

  Definition unfolder_LearnHook : MEVAL.LearnHook (repr bedrock_types_r types) 
    (SymState (repr bedrock_types_r types) (tvType 0) (tvType 1)) :=
    fun prover meta_vars vars_vars st facts ext => 
      match SymMem st with
        | Some m =>
          match UNF.forward hints prover 10 facts
            {| UNF.Vars := vars_vars
             ; UNF.UVars := meta_vars
             ; UNF.Heap := m
             |}
            with
            | {| UNF.Vars := vs ; UNF.UVars := us ; UNF.Heap := m |} =>
              (** assert (us = meta_vars) **)
              ({| SymMem := Some m
                ; SymRegs := SymRegs st
                ; SymPures := SymPures st ++ SH.pures m
                |}, qex (skipn (length vars_vars) vs) QBase)
          end
        | None => (st, QBase)
      end.

  Variable funcs : functions (repr bedrock_types_r types).
  Variable preds : SEP.predicates (repr bedrock_types_r types) (tvType 0) (tvType 1).
  Hypothesis hints_correct : UNF.hintsSoundness funcs preds hints.

  (** TODO : move to SymILProofs **)
  Lemma stateD_WellTyped_sheap : forall uvars vars cs stn_st s SymRegs SymPures,
    stateD funcs preds uvars vars cs stn_st {| SymMem := Some s; SymRegs := SymRegs; SymPures := SymPures |} ->
    SH.WellTyped_sheap (typeof_funcs funcs) (UNF.SE.typeof_preds preds) (typeof_env uvars) (typeof_env vars) s = true.
  Proof.
    clear. intros. unfold stateD in H.
    destruct stn_st. destruct SymRegs. destruct p. intuition. generalize H. clear; intros.
    rewrite sepFormula_eq in H. unfold sepFormula_def in *. simpl in H.
    rewrite SH.WellTyped_sheap_WellTyped_sexpr.
    eapply UNF.HEAP_FACTS.SEP_FACTS.interp_WellTyped_sexpr; eauto.
  Qed.

  Theorem unfolderLearnHook_correct 
    : @MEVAL.LearnHook_correct (repr bedrock_types_r types) _ BedrockCoreEnv.pc BedrockCoreEnv.st (@unfolder_LearnHook) 
    (@stateD _ funcs preds) funcs preds.
  Proof.
    Opaque repr UNF.forward.
    unfold unfolder_LearnHook. econstructor. intros. generalize dependent 10. intros.

    destruct ss. simpl in *.
    destruct SymMem; simpl; intros.
    { remember (UNF.forward hints P n pp
      {| UNF.Vars := typeof_env vars
        ; UNF.UVars := typeof_env uvars
        ; UNF.Heap := s |}).
      destruct u; simpl in *.
      symmetry in Hequ.
      eapply UNF.forwardOk with (cs := cs) in Hequ; eauto using typeof_env_WellTyped_env.
      Focus 2. simpl.
      eapply stateD_WellTyped_sheap. eauto. simpl in *.
      inversion H2; clear H2; subst.

      apply quantD_qex_QEx. simpl.
      unfold stateD in *. destruct stn_st. destruct SymRegs. destruct p. intuition.
      repeat match goal with
               | [ H : match ?X with _ => _ end |- _ ] => 
                 consider X; intros; try contradiction
             end.
      intuition; subst.
      rewrite Hequ in H.
      rewrite sepFormula_eq in H. unfold sepFormula_def in *. simpl in H.
      eapply UNF.ST_EXT.interp_existsEach in H. destruct H.
      apply existsEach_sem. exists x. destruct H. split.
      unfold typeof_env. simpl in *. rewrite map_length. rewrite <- H.
      apply map_ext. auto.
      rewrite <- app_nil_r with (l := uvars).
      repeat erewrite exprD_weaken by eassumption. intuition.
      rewrite <- app_nil_r with (l := vars ++ x). rewrite <- UNF.HEAP_FACTS.SEP_FACTS.sexprD_weaken.
      apply interp_satisfies. intuition. apply SEP.ST.HT.satisfies_memoryIn.
      apply AllProvable_app' in H4. destruct H4. repeat apply AllProvable_app; eauto using AllProvable_weaken.
      rewrite app_nil_r. eapply SH.sheapD_pures. eapply H6.
      rewrite app_nil_r. eapply SH.sheapD_pures. eapply H6. }
    { inversion H2. subst. simpl. auto. }
  Qed.
  Transparent UNF.forward.
End unfolder_learnhook.

(** Unfortunately, most things can change while evaluating a stream,
 ** so we have to move it outside the sections
 **)
Section stream_correctness.
  Variable types' : list type.
  Notation TYPES := (repr bedrock_types_r types').

  Notation pcT := (tvType 0).
  Notation tvWord := (tvType 0).
  Notation stT := (tvType 1).
  Notation tvState := (tvType 2).
  Notation tvTest := (tvType 3).
  Notation tvReg := (tvType 4).

  Variable funcs' : functions TYPES.
  Notation funcs := (repr (bedrock_funcs_r types') funcs').
  Variable preds : SEP.predicates TYPES pcT stT.

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
    interp cs (![SEP.sexprD funcs preds uvars vars (SEP.existsEach vars' P)] stn_st) ->
    exists env', map (@projT1 _ _) env' = vars' /\
      interp cs (![SEP.sexprD funcs preds uvars (rev env' ++ vars) P] stn_st).
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
          qstateD funcs preds uvars vars cs (stn, st) QBase
          {| SymMem := None
           ; SymRegs := (sp, rp, rv)
           ; SymPures := pures
           |}.
  Proof.
    Opaque repr.
    unfold qstateD. intros. simpl in *.
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
        forall (sh : SEP.sexpr TYPES pcT stT) (hashed : SH.SHeap TYPES pcT stT) vars',
          SH.hash sh = (vars', hashed) ->
          forall (cs : codeSpec W (settings * state)) (stn : settings),
            interp cs (![SEP.sexprD funcs preds uvars vars sh] (stn, st)) ->
            qstateD funcs preds uvars vars cs (stn, st) (QEx (rev vars') QBase)
              {| SymMem := Some hashed
               ; SymRegs := (sp, rp, rv)
               ; SymPures := pures
               |}.
  Proof.
    unfold qstateD. intros. simpl.
    generalize (SH.hash_denote funcs preds uvars nil cs sh). rewrite H3. simpl in *.
    intro XX. rewrite XX in H4. 

    apply interp_pull_existsEach in H4. destruct H4. intuition.
    rewrite <- H5. rewrite app_nil_r in *. apply existsEach_sem.
    exists (rev x). split; eauto. unfold typeof_env. rewrite map_rev. auto.

    change (rev x) with (nil ++ rev x).
    rewrite <- app_nil_r with (l := uvars).
    repeat (erewrite exprD_weaken by eassumption). intuition.
    rewrite app_nil_r. intuition eauto. 

    apply AllProvable_app; auto.
    { eapply AllProvable_weaken. eauto. }
    { rewrite sepFormula_eq in H6. unfold sepFormula_def in H6. simpl in H6.
      eapply SH.sheapD_pures. 
      unfold SEP.ST.satisfies. simpl in *. rewrite app_nil_r. eauto. }
  Qed.

End stream_correctness.


(** Reification **)

(* Reify the instructions *)
Ltac collectTypes_loc isConst l Ts k :=
  match l with
    | Reg _ => k Ts
    | Imm ?i => ReifyExpr.collectTypes_expr isConst i Ts k
    | Indir _ ?i => ReifyExpr.collectTypes_expr isConst i Ts k
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

Ltac collectTypes_lvalue isConst l Ts k :=
  match l with
    | LvReg _ => k Ts
    | LvMem ?l => collectTypes_loc isConst l Ts k
  end.

Ltac reify_lvalue isConst l types funcs uvars vars k :=
  match l with
    | LvReg ?r => let l := constr:(@SymLvReg types r) in k uvars funcs l 
    | LvMem ?l => 
      reify_loc isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        let l := constr:(@SymLvMem types l) in k uvars funcs l)
  end.

Ltac collectTypes_rvalue isConst r Ts k :=
  match r with
    | RvLval ?l => collectTypes_lvalue isConst l Ts k
    | RvImm ?i => ReifyExpr.collectTypes_expr isConst i Ts k
    | RvLabel _ => let Ts := Reflect.cons_uniq label Ts in k Ts
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

Ltac collectTypes_instr isConst i Ts k :=
  match i with
    | Assign ?l ?r =>
      collectTypes_lvalue isConst l Ts ltac:(fun Ts => 
        collectTypes_rvalue isConst r Ts k)
    | Binop ?l ?r1 _ ?r2 =>
      collectTypes_lvalue isConst l Ts ltac:(fun Ts => 
        collectTypes_rvalue isConst r1 Ts ltac:(fun Ts =>
          collectTypes_rvalue isConst r2 Ts k ))
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

Ltac collectTypes_instrs isConst is Ts k :=
  match is with
    | nil => k Ts
    | ?i :: ?is => 
      collectTypes_instr isConst i Ts ltac:(fun Ts =>
        collectTypes_instrs isConst is Ts k)
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
    | Rp => true
    | Rv => true
    | Sp => true
    | String.EmptyString => true
    | String.String ?e1 ?e2 =>
      match isConst e1 with
        | true => isConst e2
        | _ => false
      end
    | Ascii.Ascii ?a ?b ?c ?d ?e ?f ?g ?h =>
      match isConst a with
        | true =>
          match isConst b with
            | true =>
              match isConst c with
                | true =>
                  match isConst d with
                    | true =>
                      match isConst e with
                        | true =>
                          match isConst f with
                            | true =>
                              match isConst g with
                                | true =>
                                  match isConst h with
                                    | true => true
                                    | _ => false
                                  end
                                | _ => false
                              end
                            | _ => false
                          end
                        | _ => false
                      end
                    | _ => false
                  end
                | _ => false
              end
            | _ => false
          end
        | _ => false
      end
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

Ltac clear_instrs ins :=
  match ins with
    | tt => idtac
    | ((_,?H), ?ins) => clear H; clear_instrs ins
  end.

Ltac collectAllTypes_instrs is Ts k :=
  match is with
    | tt => k Ts
    | (((?l,?r), _), ?is) =>
       collectTypes_rvalue ltac:(isConst) l Ts ltac:(fun Ts =>
         collectTypes_rvalue ltac:(isConst) r Ts ltac:(fun Ts =>
          collectAllTypes_instrs is Ts k))
    | ((?i, _), ?is) =>
      collectTypes_instrs ltac:(isConst) i Ts ltac:(fun Ts =>
        collectAllTypes_instrs is Ts k)
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
      let Ts := constr:(Reflect.Tnil) in
      collectAllTypes_instrs i Ts ltac:(fun Ts =>
      let types_ := eval unfold bedrock_types in bedrock_types in
      let types_ := ReifyExpr.extend_all_types Ts types_ in
      let typesV := fresh "types" in
      pose (typesV := types_) ;
      let v := constr:(nil : env typesV) in
      let f := eval unfold ILEnv.bedrock_funcs in (ILEnv.bedrock_funcs typesV) in
      build_path typesV i st v v f ltac:(fun uvars funcs is sf pf =>
        assert (@istreamD typesV funcs uvars v is stn st sf)  by (exact pf)) || fail 1000)
  end.
  solve [ trivial ].
Abort.

Module Tactics.

Section apply_stream_correctness.
  Variable types' : list type.
  Notation TYPES := (repr bedrock_types_r types').

  Notation pcT := BedrockCoreEnv.pc.
  Notation tvWord := (tvType 0).
  Notation stT := BedrockCoreEnv.st.
  Notation tvState := (tvType 2).
  Notation tvTest := (tvType 3).
  Notation tvReg := (tvType 4).

  Variable funcs' : functions TYPES.
  Notation funcs := (repr (bedrock_funcs_r types') funcs').
  Variable preds : SEP.predicates TYPES pcT stT.

  Variable algos : ILAlgoTypes.AllAlgos TYPES.
  Variable algos_correct : @ILAlgoTypes.AllAlgos_correct TYPES funcs preds algos.

  (** Unfolding may have introduced some new variables, which we quantify existentially. *)
  Fixpoint quantifyNewVars (vs : variables) (en : env TYPES) (k : env TYPES -> Prop) : Prop :=
    match vs with
      | nil => k en
      | v :: vs' => exists x, quantifyNewVars vs' (en ++ existT _ v x :: nil) k
    end.


  Definition sym_eval uvars path qs_env ss :=
    let new_pures := 
      match SymMem ss with
        | None => SymPures ss
        | Some m => SH.pures m ++ SymPures ss
      end in
    let prover := match ILAlgoTypes.Prover algos with
                    | None => provers.ReflexivityProver.reflexivityProver
                    | Some p => p
                  end in
    let meval := match ILAlgoTypes.MemEval algos with
                   | None => MEVAL.Default.MemEvaluator_default _ _ _ 
                   | Some me => me
                 end in
    let unfolder := match ILAlgoTypes.Hints algos with
                      | None => @MEVAL.LearnHookDefault.LearnHook_default _ _
                      | Some h => unfolder_LearnHook h 
                    end in
    let facts := Summarize prover new_pures in
    let uvars := uvars ++ gatherAll qs_env in
    let vars := gatherEx qs_env in
    (** initial unfolding **)
    let (ss,qs) := unfolder prover uvars vars ss facts new_pures in
    @sym_evalStream _ prover meval unfolder facts path (appendQ qs qs_env) (uvars ++ gatherAll qs) (vars ++ gatherEx qs) ss.

  Lemma stateD_AllProvable_pures : forall meta_env vars stn_st ss cs,
    stateD funcs preds meta_env vars cs stn_st ss ->
    AllProvable funcs meta_env vars
    match SymMem ss with
      | Some m0 => SH.pures m0 ++ SymPures ss
      | None => SymPures ss
    end.
  Proof.
    Opaque repr.
    clear. unfold stateD. destruct ss; simpl. destruct stn_st. destruct SymRegs. destruct p.
    intuition. destruct SymMem; auto. apply AllProvable_app' in H2; apply AllProvable_app; intuition.
  Qed.

  Theorem Apply_sym_eval_with_eq : forall stn meta_env sound_or_safe st path,   
    istreamD funcs meta_env nil path stn st sound_or_safe ->
    forall cs qs ss res,
      qstateD funcs preds meta_env nil cs (stn,st) qs ss ->
      sym_eval (typeof_env meta_env) path qs ss = res ->
      match res with
        | Safe qs' ss' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            match sound_or_safe with
              | None => False
              | Some (st') => stateD funcs preds meta_env vars_env cs (stn, st') ss'
              end)
        | SafeUntil qs' ss' is' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            exists st' : state,
              stateD funcs preds meta_env vars_env cs (stn, st') ss' /\
              istreamD funcs meta_env vars_env is' stn st' sound_or_safe)
      end.
  Proof.
    intros. unfold sym_eval in *.
    assert (PC : ProverT_correct
              match ILAlgoTypes.Prover algos with
              | Some p => p
              | None => ReflexivityProver.reflexivityProver
              end (repr (bedrock_funcs_r types') funcs)).
    { generalize (ILAlgoTypes.Acorrect_Prover algos_correct).
      destruct (ILAlgoTypes.Prover algos); intros; auto.
      apply ReflexivityProver.reflexivityProver_correct. }
    generalize dependent (match ILAlgoTypes.Prover algos with
                            | Some p => p
                            | None => ReflexivityProver.reflexivityProver
                          end).
    assert (MC : SymILProofs.MEVAL.MemEvaluator_correct
      match ILAlgoTypes.MemEval algos with
      | Some me => me
      | None =>
          MEVAL.Default.MemEvaluator_default (repr BedrockCoreEnv.core TYPES)
            pcT stT
      end (repr (bedrock_funcs_r types') funcs) preds tvWord tvWord
      (IL_mem_satisfies (ts:=types')) (IL_ReadWord (ts:=types'))
      (IL_WriteWord (ts:=types'))).
    { generalize (ILAlgoTypes.Acorrect_MemEval algos_correct).
      destruct (ILAlgoTypes.MemEval algos); auto; intros.
      apply SymIL.MEVAL.Default.MemEvaluator_default_correct. }
    generalize dependent (match ILAlgoTypes.MemEval algos with
                            | Some me => me
                            | None => MEVAL.Default.MemEvaluator_default (repr BedrockCoreEnv.core TYPES) pcT stT
                          end).
    match goal with
      | [ |- context [ ?X ] ] =>
        match X with 
          | match ILAlgoTypes.Hints _ with _ => _ end =>
            assert (LC : SymILProofs.MEVAL.LearnHook_correct (types_ := TYPES) (pcT := tvType 0) (stT := tvType 1) X
              (stateD funcs preds) (repr (bedrock_funcs_r types') funcs) preds); [ | generalize dependent X ]
        end
    end.
    { generalize (ILAlgoTypes.Acorrect_Hints algos_correct).     
      destruct (ILAlgoTypes.Hints algos); auto; intros.
      { apply (@unfolderLearnHook_correct types' h funcs preds H1). } 
      { apply SymIL.MEVAL.LearnHookDefault.LearnHook_default_correct. } }
    intros l LC m MC p ? PC.
    match goal with 
      | [ H : context [ l ?A ?B ?C ?D ?E ?F ] |- _ ] =>
        consider (l A B C D E F); intros
    end.
    unfold qstateD in *. destruct res.
    Opaque stateD.
    { destruct (SymILProofs.SymIL_Correct.sym_evalStream_quant_append _ _ _ _ _ _ _ _ _ H2).
      subst. rewrite <- appendQ_assoc. rewrite quantD_app. eapply quantD_impl; eauto; intros. clear H0.
      simpl in *.
      match goal with 
        | [ H : context [ @Summarize _ ?A ?B ] |- _ ] => 
          assert (AP : AllProvable funcs (meta_env ++ b) a B); [ eauto using stateD_AllProvable_pures |
            assert (VF : Valid PC (meta_env ++ b) a (Summarize A B)); 
              [ clear H; eauto using Summarize_correct | generalize dependent (Summarize A B); generalize dependent B ; intros ] ]
      end.
      eapply (@SymILProofs.MEVAL.hook_sound _ _ _ _ _ _ _ _ LC _ PC (meta_env ++ b) a cs (stn,st)) in H5; eauto.
      2: etransitivity; [ | eapply H1 ]. 2: f_equal; eauto. 2: rewrite typeof_env_app; f_equal; auto.
      rewrite quantD_app. eapply quantD_impl; eauto; intros. simpl in *.

      eapply (@SymILProofs.SymIL_Correct.evalStream_correct_Safe TYPES funcs preds _ PC _ MC _ LC sound_or_safe cs
        stn path f s QBase x s0 ((typeof_env meta_env ++ gatherAll qs) ++ gatherAll q) (gatherEx qs ++ gatherEx q) (appendQ q qs)
        H2).
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. f_equal; auto. }
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. }
      { apply SymILProofs.SymIL_Correct.istreamD_weaken with (B := b ++ b0) (D := a ++ a0) in H.
        rewrite repr_idempotent. rewrite app_ass. apply H. }
      { simpl. intuition. eapply Valid_weaken. eauto. } }
    { destruct (SymILProofs.SymIL_Correct.sym_evalStream_quant_append _ _ _ _ _ _ _ _ _ H2).
      subst. rewrite <- appendQ_assoc. rewrite quantD_app. eapply quantD_impl; eauto; intros. clear H0.
      simpl in *.
      match goal with 
        | [ H : context [ @Summarize _ ?A ?B ] |- _ ] => 
          assert (AP : AllProvable funcs (meta_env ++ b) a B); [ eauto using stateD_AllProvable_pures |
            assert (VF : Valid PC (meta_env ++ b) a (Summarize A B)); 
              [ clear H; eauto using Summarize_correct | generalize dependent (Summarize A B); generalize dependent B ; intros ] ]
      end.
      eapply (@SymILProofs.MEVAL.hook_sound _ _ _ _ _ _ _ _ LC _ PC (meta_env ++ b) a cs (stn,st)) in H5; eauto.
      2: etransitivity; [ | eapply H1 ]. 2: f_equal; eauto. 2: rewrite typeof_env_app; f_equal; auto.
      rewrite quantD_app. eapply quantD_impl; eauto; intros. simpl in *.

      eapply (@SymILProofs.SymIL_Correct.evalStream_correct_SafeUntil TYPES funcs preds _ PC _ MC _ LC sound_or_safe cs
        stn path f s QBase x s0); eauto.  (*((typeof_env meta_env ++ gatherAll qs) ++ gatherAll q) (gatherEx qs ++ gatherEx q) (appendQ q qs)
        H2). *)
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. f_equal; auto. }
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. }
      { apply SymILProofs.SymIL_Correct.istreamD_weaken with (B := b ++ b0) (D := a ++ a0) in H.
        rewrite repr_idempotent. rewrite app_ass. apply H. }
      { simpl. intuition. eapply Valid_weaken. eauto. } }
  Qed.

  Theorem Apply_sym_eval : forall stn meta_env sound_or_safe st path,
    istreamD funcs meta_env nil path stn st sound_or_safe ->
    forall cs qs ss,
      qstateD funcs preds meta_env nil cs (stn,st) qs ss ->
      match sym_eval (typeof_env meta_env) path qs ss with
        | Safe qs' ss' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            match sound_or_safe with
              | None => False
              | Some (st') => stateD funcs preds meta_env vars_env cs (stn, st') ss'
              end)
        | SafeUntil qs' ss' is' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            exists st' : state,
              stateD funcs preds meta_env vars_env cs (stn, st') ss' /\
              istreamD funcs meta_env vars_env is' stn st' sound_or_safe)
      end.
  Proof. intros. eapply Apply_sym_eval_with_eq; eauto. Qed.

End apply_stream_correctness.

Module SEP_REIFY := ReifySepExpr.ReifySepExpr SEP.

(** NOTE:
 ** - [isConst] is an ltac function of type [* -> bool]
 ** - [ext] is the extension. it is a value of type [TypedPackage]
 ** - [simplifier] is an ltac that takes a hypothesis names and simplifies it
 **     (this should be implmented using [cbv beta iota zeta delta [ ... ] in H])
 **     (it is recommended/necessary to call [sym_evaluator] or import its simplification)
 **)
Ltac sym_eval isConst ext simplifier :=
(*TIME  start_timer "sym_eval:init" ; *)
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
        let SF := eval unfold empB, injB, injBX, starB, exB, hvarB in SF in
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
          repr_combine listToRepr listOptToRepr nil_Repr
          ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
          ILAlgoTypes.PACK.applyTypes
          ILAlgoTypes.PACK.applyFuncs
          ILAlgoTypes.PACK.applyPreds
          tl map repr
          ILAlgoTypes.PACK.CE.core
          bedrock_types_r bedrock_funcs_r
          TacPackIL.ILAlgoTypes.Env
        ] in ls
      | _ => 
        eval cbv beta iota zeta delta [
          sym ext
          repr_combine listToRepr listOptToRepr nil_Repr
          ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
          ILAlgoTypes.PACK.applyTypes
          ILAlgoTypes.PACK.applyFuncs
          ILAlgoTypes.PACK.applyPreds

          map tl repr
          ILAlgoTypes.PACK.CE.core
          bedrock_types_r bedrock_funcs_r
          TacPackIL.ILAlgoTypes.Env
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
(*TIME                  stop_timer "sym_eval:init" ; *)
(*TIME                  start_timer "sym_eval:gather_instrs" ; *)
                  let all_instrs := get_instrs st in
                  let all_props := 
                    ReifyExpr.collect_props ltac:(SEP_REIFY.reflectable shouldReflect)
                  in
                  let pures := ReifyExpr.props_types all_props in
                  let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
(*TIME                  stop_timer "sym_eval:gather_instrs" ; *)
                  (** collect the raw types **)
(*TIME                  start_timer "sym_eval:reify" ; *)
                  let Ts := constr:(Reflect.Tnil) in
                  let Ts k := 
                    match SF with
                      | tt => k Ts
                      | (?SF,_) => (** TODO: a little sketchy since it is in CPS **)
                        SEP_REIFY.collectTypes_sexpr ltac:(isConst) SF Ts k 
                    end
                  in
                    Ts ltac:(fun Ts => 
                  collectAllTypes_instrs all_instrs Ts ltac:(fun Ts => 
                  ReifyExpr.collectTypes_exprs ltac:(isConst) regs Ts ltac:(fun Ts => 
                  ReifyExpr.collectTypes_exprs ltac:(isConst) pures Ts ltac:(fun Ts => 
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
                  let types_ := reduce_repr tt (ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext) nil) in
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
                  let funcs := reduce_repr tt (ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext) typesV (repr (bedrock_funcs_r typesV) nil)) in
                   (** build the base sfunctions **)
(*                  let preds := constr:(@nil (@SEP.ssignature typesV pcT stT)) in *)
                  let preds := reduce_repr tt (ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext) typesV nil) in
                  (** reflect the expressions **)
                  ReifyExpr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
                  let proofs := ReifyExpr.props_proof all_props in
                  
                  ReifyExpr.reify_expr ltac:(isConst) rp_v typesV funcs uvars vars ltac:(fun uvars funcs rp_v  => 
                  ReifyExpr.reify_expr ltac:(isConst) sp_v typesV funcs uvars vars ltac:(fun uvars funcs sp_v =>  

                  ReifyExpr.reify_expr ltac:(isConst) rv_v typesV funcs uvars vars ltac:(fun uvars funcs rv_v => 
                    let finish H  :=
(*TIME                      start_timer "sym_eval:cleanup" ; *)
                      ((try exact H) ||
                       (let rec destruct_exs H :=
                         match type of H with
                           | Logic.ex _ =>
                             destruct H as [ ? H ] ; destruct_exs H
                           | forall x : ?T, _ =>
                             let n := fresh in
                             evar (n : T); 
                             let e := eval cbv delta [ n ] in n in 
                             specialize (H e)                             
                           | (_ /\ (_ /\ _)) /\ (_ /\ _) =>
                             destruct H as [ [ ? [ ? ? ] ] [ ? ? ] ];
                               repeat match goal with
                                        | [ H' : _ /\ _ |- _ ] => destruct H'
                                      end
                           | False => destruct H
                           | ?G =>
                             fail 100000 "bad result goal" G
                         end
                        in let fresh Hcopy := fresh "Hcopy" in
                          let T := type of H in
                            assert (Hcopy : T) by apply H; clear H; destruct_exs Hcopy))
(*TIME                    ;  stop_timer "sym_eval:cleanup" *)
                    in
                    build_path typesV all_instrs st uvars vars funcs ltac:(fun uvars funcs is fin_state is_pf => 
                      match SF with
                        | tt => 
(*TIME                          stop_timer "sym_eval:reify" ; *)
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
                            (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                            stn uvars fin_state st is is_pf) in H_stateD)
                          || fail 100000 "couldn't apply sym_eval_any! (non-SF case)"); 
                          first [ simplifier typesV funcsV predsV H_stateD | fail 100000 "simplifier failed! (non-SF)" ] ;
                          try clear typesV funcsV predsV ;
                          first [ finish H_stateD (*; clear_instrs all_instrs*) | fail 100000 "finisher failed! (non-SF)" ]
                        | (?SF, ?H_interp) =>
                          SEP_REIFY.reify_sexpr ltac:(isConst) SF typesV funcs pcT stT preds uvars vars 
                          ltac:(fun uvars funcs preds SF =>
(*TIME                            stop_timer "sym_eval:reify" ; *)
(*TIME                            start_timer "sym_eval:pose" ; *)
                            let funcsV := fresh "funcs" in
                            pose (funcsV := funcs) ;
                            let predsV := fresh "preds" in
                            pose (predsV := preds) ;
(*                            let ExtC := constr:(@Algos_correct ext typesV funcsV predsV) in *)
(*TIME                            stop_timer "sym_eval:pose" ; *)
(*TIME                            start_timer "sym_eval:apply_stateD_proof" ; *)
                            apply (@stateD_proof typesV funcsV predsV
                              uvars _ sp_v rv_v rp_v 
                              sp_pf rv_pf rp_pf pures proofs SF _ _ (refl_equal _)) in H_interp ;
(*TIME                            stop_timer "sym_eval:apply_stateD_proof" ; *)
(*TIME                            start_timer "sym_eval:apply_sym_eval" ; *)
                            ((apply (@Apply_sym_eval typesV funcsV predsV
                              (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                              stn uvars fin_state st is is_pf) in H_interp) ||
                             (idtac "couldn't apply sym_eval_any! (SF case)"; 
                               first [ 
                                 generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars fin_state st is is_pf) ; idtac "6" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars fin_state st) ; idtac "5"  
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars) ; idtac "4" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)); idtac "3" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV)) ; generalize (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV) ; idtac "2" 
                               | generalize (@Apply_sym_eval typesV funcsV predsV) ; idtac "1"  
                               ])) ;
(*TIME                             stop_timer "sym_eval:apply_sym_eval" ; *)
(*TIME                             start_timer "sym_eval:simplify" ; *)
                            first [ simplifier typesV funcsV predsV H_interp | fail 100000 "simplifier failed! (SF)" ] ;
(*TIME                             stop_timer "sym_eval:simplify" ; *)
(*TIME                             start_timer "sym_eval:clear" ; *)
                            try clear typesV funcsV predsV ;
(*TIME                             stop_timer "sym_eval:clear" ; *)
                            first [ finish H_interp ; clear_instrs all_instrs | fail 100000 "finisher failed! (SF)" ])
                      end)))))  ))))
              end
          end
      end
  end.

(*
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
      ReifyExpr.default_type

      SH.liftSHeap
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
      
      MEVAL.sread_word MEVAL.swrite_word
      
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
      mentionsU
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
      equiv_dec (* UNF.substExpr *) Unfolder.FM.add 
      Unfolder.allb andb length map app exprSubstU
      unfolder_LearnHook
      UNF.default_hintsPayload UNF.findWithRest'
      UNF.findWithRest

      SH.hash SH.star_SHeap SH.liftSHeap SepHeap.MM.mmap_join map (* UNF.substExpr *)
      rev_append

      Unfolder.FM.fold Unfolder.FM.add

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

*)

End Tactics.
