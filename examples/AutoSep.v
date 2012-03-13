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
        forall SF R,
          SEP.hash SF = (nil, R) ->
          forall funcs' sfuncs',
            match SEP.sepCancel {| SepExpr.impures := SepExpr.impures L ; SepExpr.pures := hyps ++ SepExpr.pures L ; SepExpr.other := SepExpr.other L |} R with
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
                          subst types_extV; subst typesV; clear path ; 
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
                              Env.repr Env.updateAt
                            ] in H'   ; 
                          match goal with
                            | [ |- False ] => try assumption
                            | [ H_spec : ?specs ?X = Some _ 
                              , H_cond : forall x, interp ?specs _ 
                              |- exists pre' : spec W (settings * state), ( ?specs ?Z = Some pre' /\ interp ?specs (pre' ?Y)) ] =>
                              open_stateD H' ;
                              let eq_pf := fresh in
                              assert (eq_pf : X = Z) by congruence ;
                              apply (@goto_proof specs X Z _ H_spec eq_pf Y _ (H_cond Y)) ;
                              autorewrite with sepFormula; cbv beta iota zeta delta [ substH subst eatLast ];
                              (* I don't want to mess up my [interp] lemma, otherwise I would call [propxFo] or [ho] *) 
                              repeat (apply And_I || apply Inj_I) ;
                              (try match goal with
                                    | [ |- valid ?specs nil ?S ] => change (valid specs nil S) with (interp specs S)
                                  end ;
                              unfold starB, hvarB, hpropB) ;
                              match goal with
                                | [ H_interp : interp _ (![ @SEP.sexprD _ _ _ _ _ _ _ (SEP.sheapD ?L) ] ?stn_st)
                                  , H_allProvable : Expr.AllProvable _ _ _ _ 
                                  |- interp _ (![ ?SF ] ?stn_st) ] =>
                                  SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars 
                                    ltac:(fun funcs' sfuncs' SF =>
                                      let funcs_ext := extension funcs funcs' in
                                      let sfuncs_ext := extension sfuncs sfuncs' in
                                      (apply (@interp_interp_cancel _ funcs sfuncs uvars vars L stn_st cs 
                                        H_interp _ H_allProvable SF _ (refl_equal _) funcs_ext sfuncs_ext)) 
                                       || fail 1000000 "couldn't apply") ;
                                      cbv beta iota zeta delta
                                        [ SEP.sheapD SEP.sepCancel
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
                                          

                                          SEP.himp SEP.sexprD Expr.Impl 
                                          Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation 
                                          tvTest
                                          SepExpr.SDenotation SepExpr.SDomain
                                          EquivDec.nat_eq_eqdec  
                                          tvWord
                                        ]
                                | [ |- _ ] =>
                                  repeat match goal with
                                           | [ H : Expr.AllProvable _ _ _ _ |- _ ] =>
                                             unfold Expr.AllProvable, Expr.Provable in H; simpl in H
                                         end
                              end
                            | [ |- ?G ] => fail 1000000 "got something weird!" G
                          end
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
    simpl; intuition congruence.
    unfold Expr.AllProvable, Expr.Provable in H2; simpl in H2. intuition; subst. admit.

  Time sym_eval ltac:(isConst) unfolder (CORRECTNESS ptsto_evaluator) tt tt tt simplifier.
    simpl; intuition congruence.
    unfold Expr.AllProvable, Expr.Provable in H2; simpl in H2. intuition; subst. admit.
Time Qed.

(*

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
                        | _ :: _ :: _ :: _ :: _ :: ?funcs_ext =>
                          apply (@stateD_proof types_extV funcs uvars vars sfuncs _ sp_v rv_v rp_v 
                            sp_pf rv_pf rp_pf pures proofs SF _ (refl_equal _)) in H' ;
                          eapply (@sym_eval_any _ _ C types_extV funcs_ext sfuncs stn uvars vars _ _ _ path) in H' ;
                          subst types_extV; subst typesV; clear path ; 
                          unfolder H' ;
                          cbv beta iota zeta delta
                            [ sym_evalInstrs sym_evalInstr sym_evalLval sym_evalRval sym_evalLoc sym_evalStream sym_assertTest
                              sym_setReg sym_getReg
                              SymIL.PLUGIN.sym_read SymIL.PLUGIN.sym_write SymIL.PLUGIN.Build_SymEval
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
                              Env.repr Env.updateAt
                            ] in H' ; 
                          denote_evaluator H'
                      end))))))
                end
            end
        end
    end.

  denote_evaluator H2.
  simple apply stateD_regs in H2.
  cbv iota zeta beta delta 
    [ stateD SEP.star_SHeap SepExpr.FM.add SepExpr.FM.empty SEP.liftSHeap 
      SEP.multimap_join
      SepExpr.other SepExpr.pures SepExpr.impures SepExpr.FM.find
      SepExpr.FM.fold SepExpr.FM.map
      Compare_dec.lt_eq_lt_dec nat_rec nat_rect
      app map
    ] in H3.
  simpl in H3.
  

  rewrite heq_star_comm. auto.

  repeat match goal with
            | [ H : _ /\ (_ /\ _) |- _ ] =>
              progress (
                (try rewrite <- (proj1 H) in * ) ;
                (try rewrite <- (proj2 (proj2 H)) in * ) ;
                (try rewrite <- (proj1 (proj2 H)) in * )
              ) ; try clear H
          end.
  ho. specialize (H6 (stn, st)). autorewrite with sepFormula in *. unfold substH in *. simpl in *.
  unfold starB.
  rewrite heq_star_comm. auto.
Qed.
*)


(*symeval types_ext funcs_ext sfuncs knowns evals uvars vars 
      sis stateD_pf success failure :=
                          apply (@hash_interp types_ext funcs_ext sfuncs SF _ (refl_equal _) uvars vars) in H' ;
                          match type of H' with
                            | PropX.interp _ (![ @SEP.sexprD _ _ _ _ _ _ _ (SEP.sheapD ?SH) ] _) =>
                              (** TODO: I need to do something with [pures] **)

                                symeval types_ext funcs_ext sfuncs knowns evals uvars vars 
                                  rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis SH H'
                                  ltac:(fun st stateD_pf rws =>
                                    idtac "succeeded" ;
                                    let rec rewrite_regs rws :=
                                      match rws with
                                        | tt => idtac
                                        | (_, tt) => idtac
                                        | (?H, ?rws) =>
                                          rewrite_regs rws ;
                                          (try rewrite <- (proj1 H) in * ) ;
                                          (try rewrite <- (proj2 (proj2 H)) in * ) ;
                                          (try rewrite <- (proj1 (proj2 H)) in * ) ; 
                                          clear H
                                      end
                                    in
                                    idtac rws ;
                                    rewrite_regs rws ;  
                                    instantiate ;
                                    repeat match goal with
                                             | [ H : forall x : settings * state, _ |- _ ] =>
                                               specialize (H (stn, st)); 
                                               autorewrite with sepFormula in H; unfold substH, starB in H; simpl in H
                                           end;
                                    try (eexists; split; [ eassumption | instantiate; eapply Imply_E; try eassumption; propxFo ]);
                                    match goal with
                                      | [ H : interp cs (SepIL.SepFormula.sepFormula ?SF ?X)
                                        |- interp cs (SepIL.SepFormula.sepFormula ?SF' ?X) ] =>
                                      idtac "found it!"
                                      | [ |- _ ] => idtac "didn't find it!"
                                    end
                                    )
                                  ltac:(fun _ => idtac "failed!"))
                          end
*)

(*
(** Identity function, using a simple calling convention *)

Definition identityS : assert := st ~> Ex a, ![ st#Sp ==> a ] st /\ st#Rp @@ (st' ~> [| st'#Rv = a /\ st'#Sp = st#Sp |]).
Definition identity := bmodule "identity" {{
  bfunction "identity" [identityS] {
    Rv <- $[Sp];;
    Goto Rp
  }
}}.
Theorem identityOk : moduleOk identity.
  structured; ho. sepRead; reflexivity.
Qed.

(** One-word memory preservation *)
Definition preserveS : assert := st ~> ![ $0 ==> $0 ] st /\ st#Rp @@ (st' ~> ![ $0 ==> $0 ] st').
Definition preserve := bmodule "preserve" {{
  bfunction "preserve" [preserveS] {
    Goto Rp
  }
}}.
Theorem preserveOk : moduleOk preserve.
  structured. ho. autorewrite with sepFormula. assumption.
Qed.

(** Write *)
Definition writeS : assert := st ~> Ex v, ![ $0 ==> v ] st /\ st#Rp @@ (st' ~> ![ $0 ==> $0 ] st').
Definition write := bmodule "write" {{
  bfunction "write" [writeS] {
    $[0] <- 0;;
    Goto Rp
  }
}}.
Theorem writeOk : moduleOk write.
  structured; ho. specialize (H3 (stn, x)). autorewrite with sepFormula in *; eauto.
  rewrite sepFormula_eq in *.
  generalize dependent H0.
  propxFo. unfold WriteWord. 
 info propxFo.
Abort.

(** Unknown memory *)
Definition unknownS : assert := st ~> Ex g0, ![ st#Sp ==> g0 ] st /\ st#Rp @@ (st' ~> Ex g1, ![ st'#Sp ==> g1 ] st' /\ [| st#Sp = st'#Sp |]).
Definition unknown := bmodule "unknown" {{
  bfunction "unknown" [unknownS] {
    Goto Rp
  }
}}.
Theorem unknownOk : moduleOk unknown.
  structured. ho. exists x. autorewrite with sepFormula in *. ho. propxFo. (* simplify_fwd *)
Qed.


(** Constant memory swap function *)
Definition swapS : assert := st ~> Ex pa, Ex pb, Ex a, Ex b, Ex g0, Ex g1, Ex g2, Ex g3,
  ![ st#Sp ==> pa * (st#Sp^+$4) ==> pb * (st#Sp^-$4) ==> g0 * (st#Sp^-$8) ==> g1 * pa ==> a * pb ==> b ] st /\
  st#Rp @@ (st' ~> ![ st#Sp ==> pa * (st#Sp^+$4) ==> pb * (st#Sp^-$4) ==> g2 * (st#Sp^-$8) ==> g3 * pa ==> a * pa ==> b ] st').
Definition swap := bmodule "swap" {{
  bfunction "swap" [swapS] {
    Goto Rp
  }
}}.
Theorem swapOk : moduleOk swap.
Abort.

(** Swap function *)

(* stack grows down, top argument is on bottom. This is mostly forced
by the fact that Indir only takes positive offsets. *)
Definition swapS' : assert := st ~> Ex pa, Ex pb, Ex a, Ex b,
  ![ st#Sp ==> pa * (st#Sp^+$4) ==> pb * pa ==> a * pb ==> b ] st /\
  st#Rp @@ (st' ~> ![ pa ==> b * pb ==> a ] st' ).
Definition swap' := bmodule "swap'" {{
  bfunction "swap'" [swapS'] {
    (* due to huge resource constraints, we need to keep Rv available to load pointer locations *)
    Sp <- Sp - 8;;
    Rv <- $[Sp+$8];;
    $[Sp] <- $[Rv];;
    Rv <- $[Sp+$12];;
    $[Sp+$4] <- $[Rv];;
    $[Rv] <- $[Sp];;
    Rv <- $[Sp+$8];;
    $[Rv] <- $[Sp+$4];;
    Sp <- Sp + 8;;
    Goto Rp
  }
}}.
Theorem swapOk : moduleOk swap.
Abort.

(** * Dirt-simple test cases for implication automation *)
Ltac isConst e :=
  match e with
    | true => true
    | false => true
    | O => true
    | S ?e => isConst e
    | _ => false
  end.

Opaque SEP.himp.

Theorem ptsto_refl : forall a v,
  a ==> v ===> a ==> v.
Proof.
  intros.
  reflect_goal ltac:(isConst) (@nil Expr.type).
  intro. SEP.canceler tt.
  reflexivity.
Qed.

Theorem ptsto_comm : forall a1 v1 a2 v2,
  a1 ==> v1 * a2 ==> v2 ===> a2 ==> v2 * a1 ==> v1.
Proof.
  intros.
  reflect_goal ltac:(isConst) (@nil Expr.type).
  intro. SEP.canceler tt. reflexivity.
Qed.


(** * Linked list ADT *)

Module Type LINKED_LIST.
  Parameter llist : list W -> W -> HProp.

  Axiom llist_nil_fwd : forall ls a, a = 0
    -> llist ls a ===> [| ls = nil |].

  Axiom llist_nil_bwd : forall ls a, a = 0
    -> [| ls = nil |] ===> llist ls a.

  Axiom llist_cons_fwd : forall ls a, a <> $0
    -> llist ls a ===> Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p.

  Axiom llist_cons_bwd : forall ls a, a <> $0
    -> (Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p) ===> llist ls a.
End LINKED_LIST.

Module LinkedList : LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint llist (ls : list W) (a : W) : HProp :=
    match ls with
      | nil => [| a = 0 |]
      | x :: ls' => Ex p, a ==> x * (a ^+ $4) ==> p * llist ls' p
    end.

  Theorem llist_nil_fwd : forall ls a, a = 0
    -> llist ls a ===> [| ls = nil |].
  Admitted.

  Theorem llist_nil_bwd : forall ls a, a = 0
    -> [| ls = nil |] ===> llist ls a.
  Admitted.

  Theorem llist_cons_fwd : forall ls a, a <> $0
    -> llist ls a ===> Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p.
  Admitted.

  Theorem llist_cons_bwd : forall ls a, a <> $0
    -> (Ex x, Ex ls', Ex p, [| ls = x :: ls' |] * a ==> x * (a ^+ $4) ==> p * llist ls' p) ===> llist ls a.
  Admitted.
End LinkedList.

*)
