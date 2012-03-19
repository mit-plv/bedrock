Require Import Bedrock.

Set Implicit Arguments.

(** * Let's read from memory! *)

Import SymIL.BedrockEvaluator.
Require Import Bedrock.sep.PtsTo2.

Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st').

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    If (Rv = 0) {
      $[0] <- 0
    } else {
      $[0] <- 0
    } ;;
    Rv <- $[0];;
    Goto Rp
  }
}}.

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
  let types := app SymIL.bedrock_types types' in
    forall funcs sfuncs uvars vars L stn_st cs,
      interp cs (![ (@SEP.sexprD types funcs pcT stT sfuncs uvars vars (SEP.sheapD L))] stn_st) ->
      forall hyps,
        Expr.AllProvable funcs uvars vars hyps ->
        forall eq_prover : Provers.EqProverT funcs,
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

Ltac sym_eval isConst unfolder C Ts Fs SFs simplifier :=
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
                    let types := eval unfold SymIL.bedrock_types in SymIL.bedrock_types in
                    let types := Expr.extend_all_types Ts types in
                    let typesV := fresh "types" in
                    pose (typesV := types);
                    let types_ext := eval simpl in (SymIL.bedrock_ext types) in
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
                                let funcs_ext := extension funcs funcs' in
                                eapply (@evalPath_cond_app types_extV funcs funcs_ext uvars vars l t r _ _ _ _ last) in H;
                                cbv iota in H ;
                                clear last ; 
                                build_path is H funcs' k))
                            | evalInstrs _ ?st _ = _ =>
                              reflect_instrs ltac:(isConst) i typesV funcs uvars vars ltac:(fun funcs' sis =>
                                let funcs_ext := extension funcs funcs' in
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
                          (unfolder H' || fail 1000000 "unfolder failed!") ;
                          cbv beta iota zeta delta
                            [ sym_evalInstrs sym_evalInstr sym_evalLval sym_evalRval sym_evalLoc sym_evalStream sym_assertTest
                              sym_setReg sym_getReg
                              SepExpr.pures SepExpr.impures SepExpr.other
                              SymMem SymRegs SymPures
                              SEP.star_SHeap SEP.liftSHeap SEP.multimap_join 
                              Expr.SemiDec_expr Expr.expr_seq_dec Expr.tvar_val_sdec Expr.Eq Expr.liftExpr
                              app map nth_error value error fold_right
                              DepList.hlist_hd DepList.hlist_tl DepList.seq_dec 
                              SepExpr.FM.find SepExpr.FM.add SepExpr.FM.remove SepExpr.FM.map SepExpr.FM.empty SepExpr.FM.fold
                              Compare_dec.lt_eq_lt_dec nat_rec nat_rect Peano_dec.eq_nat_dec sumbool_rec sumbool_rect
                              EquivDec.equiv_dec EquivDec.nat_eq_eqdec
                              f_equal 
                              bedrock_funcs SymIL.bedrock_types pcT stT tvWord
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
                              eq_sym f_equal
                              eq_rec_r eq_rect eq_rec
                              nat_rec nat_rect
                              sumbool_rec sumbool_rect
                              Expr.tvarD SymIL.BedrockEvaluator.types

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
                              SymIL.bedrock_types 
                                
                              Compare_dec.lt_eq_lt_dec Peano_dec.eq_nat_dec
                              nat_rec nat_rect
                              sumbool_rec sumbool_rect
                              eq_rec_r eq_rect eq_rec
                              SepExpr.FM.map ExprUnify.exprUnifyArgs ExprUnify.empty_Subst
                              ExprUnify.exprUnify ExprUnify.fold_left_2_opt 
                              fold_right value error map nth_error app                                       
                              pcT stT 
                              EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect 
                              eq_sym f_equal
                              ExprUnify.get_Eq
                              SymIL.BedrockEvaluator.types
                              Provers.transitivityProverRec Provers.transitivityEqProver Provers.inSameGroup
                              Provers.in_seq_dec
                              Provers.eqD Provers.eqD_seq
                              Expr.typeof comparator
                            ] in H' ; 
                          subst typesV; subst types_extV ;
                          (try assumption ||
                           destruct H' as [ [ ? [ ? ? ] ] [ ? ? ] ])
                      end))))))
                end
            end
        end
    end.

Ltac unfolder H :=
  cbv delta [ 
    ptsto_evaluator CORRECTNESS READER WRITER DEMO.expr_equal DEMO.types
    DEMO.ptsto32_ssig DEMO.ptrIndex DEMO.wordIndex
    SymEval.fold_args SymEval.fold_args_update
  ] in H.

Theorem readOk : moduleOk read.
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
    admit.

  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
    admit.
Time Qed.
