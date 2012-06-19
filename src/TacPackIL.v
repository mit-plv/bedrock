Require Import Expr SepExpr.
Require Import Prover SymEval.
Require Import Env TypedPackage.
Import List.

Require Import IL SepIL SymIL ILEnv.

Set Implicit Arguments.
Set Strict Implicit.
Require Unfolder.
Module UNF := Unfolder.Make SH ExprUnify.UNIFIER.
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
      eapply Folds.Forall_app; auto.
    destruct MemEval0; destruct MemEval1; simpl; auto. apply MEVAL.Composite.MemEvaluator_correct_composite; auto.
  Qed.

  Record TypedPackage : Type :=
  { Env   : PACK.TypeEnv
  ; Algos : forall ts, AllAlgos (PACK.applyTypes Env ts)
  ; Algos_correct : forall ts fs ps,
    @AllAlgos_correct (PACK.applyTypes Env ts) (PACK.applyFuncs Env _ fs) (PACK.applyPreds Env _ ps) (Algos ts)
  }.

  Definition EnvOf : TypedPackage -> PACK.TypeEnv := Env.

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
  
(*
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
      provers.ReflexivityProver.unfold_reflexivityProver H ;
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
     Abort.*)

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
    
(*
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
      provers.ReflexivityProver.unfold_reflexivityProver H ;
      MEVAL.Default.unfolder H ;
      sym_evaluator H.
*)
  End BedrockPackage.

  Module Tactics.

    (** Build Packages for Provers **)
    Ltac build_prover_pack prover ret :=
      let res := constr:( 
        let env :=
          {| PACK.Types := Prover.ProverTypes prover
           ; PACK.Funcs := fun ts => Prover.ProverFuncs prover (repr bedrock_types_r ts)
           ; PACK.Preds := fun ts =>
             nil_Repr (SEP.Default_predicate (repr (Prover.ProverTypes prover) (repr bedrock_types_r ts)) (tvType 0) (tvType 1))
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
           let types := repr bedrock_types_r ts in
           let funcs := repr (PACK.Funcs env types) fs in
           @Build_AllAlgos_correct types funcs ps (algos ts)
             (@Prover.Prover_correct prover types funcs)
             I I
        |})
      in
      let res := eval simpl in res in
      ret res.

    Module ProverPackTest.
      Require Provers.
      (** Test **)
      Goal TypedPackage.
        build_prover_pack provers.TransitivityProver.TransitivityProver ltac:(fun x => refine x).
      Defined.
    End ProverPackTest.

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

    Module MemPackTest.

      Goal TypedPackage.
        pose (mem := 
          {| MEVAL.MemEvalTypes := nil_Repr EmptySet_type
           ; MEVAL.MemEvalFuncs := fun ts => nil_Repr (Default_signature _)
           ; MEVAL.MemEvalPreds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
           ; MEVAL.MemEval := fun ts => @MEVAL.Default.MemEvaluator_default _ (tvType 0) (tvType 1)
           ; MEVAL.MemEval_correct := fun ts fs ps =>
             @MEVAL.Default.MemEvaluator_default_correct _ _ _ _ _ _ _ _ _ _ _
          |} : @MEVAL.MemEvaluatorPackage min_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) 
                   IL_mem_satisfies IL_ReadWord IL_WriteWord).
        build_mem_pack mem ltac:(fun x => refine x).
      Defined.
    End MemPackTest.

    (** builds a [TypedPackage] from the arguments
     ** - [hints] is a list of separation logic hints
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
            @Build_AllAlgos_correct _ _ _ (algos ts) I (PACKAGED.HintsOk hints ts fs ps) I))
      in
      let res := eval simpl in res in
      ret res.

    Definition bedrock_env : PACK.TypeEnv :=
      {| PACK.Types := nil_Repr EmptySet_type
       ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
       ; PACK.Preds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
      |}.

    Module HintsPackTest.
      Ltac isConst _ := true.
      
(*
      Goal TypedPackage.
        PACKAGED.prepareHints ltac:(fun x => x) W (prod IL.settings IL.state) ltac:(isConst) bedrock_env tt tt ltac:(fun v => 
          build_hints_pack v ltac:(fun x => refine x)).
      Defined.
*)
    End HintsPackTest.


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
      @AllAlgos_composite (Env.repr ntypesV ts)
                          (Algos l (Env.repr ntypesV ts))
                          (Algos r (Env.repr ntypesV ts))
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
  build_prover_pack provers.TransitivityProver.TransitivityProver ltac:(fun x => 
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
  End Tactics.

  Definition AlgoImpl := AllAlgos.
  Definition AlgoProof := AllAlgos_correct.
End ILAlgoTypes.

