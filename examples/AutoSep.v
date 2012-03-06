Require Import Bedrock.

Set Implicit Arguments.

(** * Let's read from memory! *)

Import SepTac.BedrockEvaluator.
Require Import Bedrock.sep.PtsTo.

Module PLUGIN_PTSTO := BedrockPtsToEvaluator SepTac.PLUGIN.

Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st).

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    If (Rv = 0) {
      $[0] <- Rv 
    } else {
      $[0] <- 0 
    } ;;
    Rv <- $[0];;
    Goto Rp
  }
}}.

Implicit Arguments sym_evalInstrs [ types' funcs' sfuncs known word_evals ].
Implicit Arguments SepExpr.FM.MBranch [ T ].
Implicit Arguments SepExpr.FM.MLeaf [ T ].
Implicit Arguments stateD [ types' funcs' sfuncs ].
Implicit Arguments sym_instrsD [ types' funcs' ].

Existing Instance PLUGIN_PTSTO.SymEval_ptsto32.
Ltac simplifier H := 
  cbv beta delta [
    PLUGIN_PTSTO.SymEval_ptsto32 PLUGIN_PTSTO.sym_read_word_ptsto32 PLUGIN_PTSTO.sym_write_word_ptsto32
    PLUGIN_PTSTO.expr_equal PLUGIN_PTSTO.types
  ] in H.

Lemma Some_inj : forall T (a b : T), a = b -> Some b = Some a.
Proof.
  intros; subst; reflexivity.
Qed.

Theorem readOk : moduleOk read.
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *.
(*
  sym_eval ltac:(isConst) simplifier.
*)
  

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
   **)
  Lemma sym_evalInstrs_sound_apply'
     : forall (types' : list Expr.type)
         (funcs' : Expr.functions (types types'))
         (sfuncs : list (SEP.ssignature (types types') pcT stT))
         (known : list nat)
         (word_evals : evaluators types' funcs' sfuncs known)
         (uvars vars : list {t : Expr.tvar & Expr.tvarD (types types') t})
         (cs : codeSpec W (settings * state)) (instrs : list instr)
         (stn : settings) (st : state),
       forall (sp rv rp : Expr.expr (types types'))
         (sh : SEP.sexpr (types types') pcT stT),
       @interp W (settings * state) cs
         (![@SEP.sexprD (types types') (funcs types' funcs') pcT stT sfuncs
              uvars vars sh] (stn, st)) ->
       @Expr.exprD (types types') (funcs types' funcs') uvars vars sp tvWord =
       @Some W (Regs st Sp) ->
       @Expr.exprD (types types') (funcs types' funcs') uvars vars rv tvWord =
       @Some W (Regs st Rv) ->
       @Expr.exprD (types types') (funcs types' funcs') uvars vars rp tvWord =
       @Some W (Regs st Rp) ->
       forall hashed : SEP.SHeap (types types') pcT stT,
       @SEP.hash (types types') pcT stT sh = (@nil Expr.tvar, hashed) ->
       forall sym_instrs : list (sym_instr (types types')),
       @sym_instrsD types' funcs' uvars vars sym_instrs =
       @Some (list instr) instrs ->
       forall st',
       evalInstrs stn st instrs = @Some state st' ->
       match
         @sym_evalInstrs types' funcs' sfuncs known word_evals sym_instrs
           {| SymMem := hashed; SymRegs := (sp, rp, rv) |}
       with
       | inl ss' => @stateD types' funcs' sfuncs uvars vars cs stn st' ss'
       | inr (ss'', is') =>
           exists st'' : state,
             match @sym_instrsD types' funcs' uvars vars is' with
             | Some instrs' =>
                 evalInstrs stn st'' instrs' = @Some state st' /\
                 @stateD types' funcs' sfuncs uvars vars cs stn st'' ss''
             | None => False
             end
       end.
  Proof.
    intros; eapply sym_evalInstrs_sound_apply; eauto.
  Qed.

  (** NOTE: This has two continuation for success and failure.
   ** success :: rp_v rp_pf sp_v sp_pf rv_v rv_pf SF sep_proof st -> ...
   ** failure :: st -> ...
   **)
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

  

  Ltac symeval simplifier types_ext funcs_ext sfuncs knowns evals uvars vars rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis is SF evalInstrs_pf sepFormula_pf success failure :=
    let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
    apply (@sym_evalInstrs_sound_apply' types_ext funcs_ext sfuncs knowns evals
      uvars vars _ is _ st sp_v rv_v rp_v SF sepFormula_pf
      sp_pf rv_pf rp_pf _ (refl_equal _) sis (refl_equal _)) in evalInstrs_pf;
    ((simplifier evalInstrs_pf ; sym_evaluator evalInstrs_pf) || fail 100 "simplification failed") ; 
    let k := type of evalInstrs_pf in 
      idtac "k = " k ;
    match k with 
      | @stateD _ _ _ _ _ _ _ _ (@Build_SymState _ ?M (?ssp, ?srp, ?srv)) =>
        (** it finished! **)
        idtac "found stateD" ;
        denote_evaluator evalInstrs_pf ;
        let k :=  type of evalInstrs_pf in 
          idtac "k2 = " k ;
        match type of evalInstrs_pf with
          | (_ = ?sp /\ (_ = ?rp /\ _ = ?rv)) /\ 
            interp _ (SepIL.SepFormula.sepFormula ?SF (_, ?st')) =>
            match goal with
              | [ H'' : evalInstrs _ st' ?is = Some ?st'' |- _ ] =>
                (** more evaluations to go **)
                clear sepFormula_pf ;
                let new_sepFormula_pf := fresh in
                let stateD_pf := fresh in
                let interp_pf := fresh in
                destruct evalInstrs_pf as [ regs_pf new_sepFormula_pf ] ;
                symeval simplifier types_ext funcs_ext sfuncs knowns evals uvars vars 
                  srp (Some_inj (proj1 (proj2 stateD_pf)))
                  ssp (Some_inj (proj1 stateD_pf))
                  srv (Some_inj (proj2 (proj2 stateD_pf)))
                  st' is SF H'' new_sepFormula_pf 
                  ltac:(fun rp_v rp_pf sp_v sp_pf rv_v rv_pf SF i st =>
                    clear H'' ; success rp_v rp_pf sp_v sp_pf rv_v rv_pf SF i st)
                  ltac:(fun z => clear H'' ; failure z)
              | [ |- _ ] =>
                (** no more evaluations, but we succeeded **)
                let a := fresh in
                let b := fresh in
                let c := fresh in
                let i := fresh in
                destruct evalInstrs_pf as [ [ a [ b c ] ] i ];
                success srp (Some_inj b) ssp (Some_inj a) srv (Some_inj c) M i st'
            end
        end
      | exists st'', _ /\ _ =>
        (** failed to symbolically evaluate **)
        let a := fresh in
        destruct evalInstrs_pf as [ a [ b c ] ] ;
        clear sepFormula_pf ;
        failure a 
    end.

  Ltac hcontains x ls :=
    match ls with
      | ( x , _ ) => true
      | ( _ , ?ls ) => hcontains x ls
      | tt => false
    end.
        
  Ltac collectAllTypes_props isConst Ts :=
    let rec collect Ts skip :=
      match goal with
        | [ H : ?X |- _ ] =>
          match X with
            | interp _ _ => fail 1
            | valid _ _ => fail 1
            | evalInstrs _ _ _ = _ => fail 1
            | _ => 
              match type of X with
                | Prop => 
                  match hcontains H skip with
                    | false => 
                      let Ts := SEP.collectTypes_expr isConst X Ts in
                        let skip := constr:((H, skip)) in
                          collect Ts skip
                  end
              end
          end
        | _ => Ts
      end
    in collect Ts tt.


  Ltac reflect_props isConst types funcs uvars vars k :=
    let rec collect skip funcs acc proofs :=
      match goal with
        | [ H : ?X |- _ ] =>
          match X with
            | interp _ _ => fail 1
            | valid _ _ => fail 1
            | evalInstrs _ _ _ = _ => fail 1
            | _ =>
              match type of X with
                | Prop => 
                  match hcontains H skip with
                    | false =>
                      SEP.reflect_expr isConst X types funcs uvars vars ltac:(fun funcs e =>
                        let skip := constr:((H, skip)) in
                        let res := constr:(e :: acc) in
                        let proofs := constr:((H, proofs)) in
                        collect skip funcs res proofs)
                  end
              end
          end
        | _ => k funcs acc proofs
      end
    in
    let acc := constr:(@nil (Expr.expr types)) in
    let proofs := tt in
    collect tt funcs acc proofs.

  (** TODO: this should take the evaluators, this makes more sense now that there are sfuncs **)
  admit.

  Theorem sym_evalInstrs_safe_apply'
     : forall (types' : list Expr.type)
         (funcs' : Expr.functions (types types'))
         (sfuncs : list (SEP.ssignature (types types') pcT stT))
         (known : list nat)
         (word_evals : evaluators types' funcs' sfuncs known)
         (uvars vars : list {t : Expr.tvar & Expr.tvarD (types types') t})
         (cs : codeSpec W (settings * state)) (instrs : list instr)
         (stn : settings) (st : state),
       forall (sp rv rp : Expr.expr (types types'))
         (hashed : SEP.SHeap (types types') pcT stT),
       @interp W (settings * state) cs
         (![@SEP.sexprD (types types') (funcs types' funcs') pcT stT sfuncs
              uvars vars (SEP.sheapD hashed)] (stn, st)) ->
       @Expr.exprD (types types') (funcs types' funcs') uvars vars sp tvWord =
       @Some W (Regs st Sp) ->
       @Expr.exprD (types types') (funcs types' funcs') uvars vars rv tvWord =
       @Some W (Regs st Rv) ->
       @Expr.exprD (types types') (funcs types' funcs') uvars vars rp tvWord =
       @Some W (Regs st Rp) ->
       forall sym_instrs : list (sym_instr (types types')),
       @sym_instrsD types' funcs' uvars vars sym_instrs =
       @Some (list instr) instrs ->
       evalInstrs stn st instrs = @None state ->
       match
         @sym_evalInstrs types' funcs' sfuncs known word_evals sym_instrs
           {| SymMem := hashed; SymRegs := (sp, rp, rv) |}
       with
       | inl _ => False
       | inr (ss'', is') =>
           exists st'' : state,
             match @sym_instrsD types' funcs' uvars vars is' with
             | Some instrs' =>
                 evalInstrs stn st'' instrs' = @None state /\
                 @stateD types' funcs' sfuncs uvars vars cs stn st'' ss''
             | None => False
             end
       end.
  Proof.
    intros. eapply sym_evalInstrs_safe_apply with (hashed := hashed); eauto.
  Admitted.

  Ltac sym_eval Ts Fs SFs simplifier :=
    match goal with
      | [ H : evalInstrs ?stn ?st ?is = ?R
        , H' : PropX.interp ?cs (SepIL.SepFormula.sepFormula ?SF (?stn, ?st)) |- _ ] =>
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
            match find_reg st Sp with
              | (?sp_v, ?sp_pf) =>
                match find_reg st Rv with
                  | (?rv_v, ?rv_pf) => 
                    let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
                    (** collect the raw types **)
                    let Ts := constr:(@nil Type) in
                    let Ts := collectTypes_instrs ltac:(isConst) is Ts in
                    let Ts := SEP.collectAllTypes_expr ltac:(isConst) Ts regs in
                    let Ts := SEP.collectAllTypes_sexpr isConst Ts (SF :: nil) in
                    let Ts := SEP.collectAllTypes_funcs Ts Fs in
                    let Ts := SEP.collectAllTypes_sfuncs Ts SFs in
                    let Ts := collectAllTypes_props isConst Ts in
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
                    reflect_props ltac:(isConst) types funcs uvars vars ltac:(fun funcs pures proofs =>
                    reflect_instrs ltac:(isConst) is types funcs uvars vars ltac:(fun funcs sis =>
                    SEP.reflect_expr ltac:(isConst) rp_v types funcs uvars vars ltac:(fun funcs rp_v =>
                    SEP.reflect_expr ltac:(isConst) sp_v types funcs uvars vars ltac:(fun funcs sp_v =>
                    SEP.reflect_expr ltac:(isConst) rv_v types funcs uvars vars ltac:(fun funcs rv_v =>
                    SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
                    match funcs with 
                      | _ :: _ :: _ :: ?funcs_ext =>
                        (** TODO: I need to do something with [pures] **)
                        build_evals sfuncs types_ext funcs_ext ltac:(fun knowns evals =>
                          idtac "OK" R;
                          match R with
                            | None => idtac
                            | Some ?st' =>
                              idtac "found st' = " st' ;
                              symeval simplifier types_ext funcs_ext sfuncs knowns evals uvars vars 
                                rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis is SF H H'
                                ltac:(fun rp_v rp_pf sp_v sp_pf rv_v rv_pf SH sep_proof st => 
                                  idtac "success";
                                  match goal with
                                    | [ H : evalInstrs ?stn ?st ?is = None 
(*                                      , H' : PropX.interp cs (SepIL.SepFormula.sepFormula ?SF (?stn, ?st)) *)
                                      |- False ] =>
                                      idtac "safety" sp_v SH sep_proof ;
                                        
                                      generalize (@sym_evalInstrs_safe_apply' types_ext funcs_ext sfuncs knowns evals
                                        uvars vars cs is stn st sp_v rv_v rp_v SH sep_proof
                                        sp_pf rv_pf rp_pf (* _ (refl_equal _) sis (refl_equal _)*) )
                                  | [ |- _ ] =>
                                    idtac "correctness"
                                  end)
                                ltac:(fun st => idtac "failure")
                          end)
                    end))))))
                end
            end
        end
    end.

  sym_eval (@nil Type) tt tt simplifier.
  simpl.
  sym_eval (@nil Type) tt tt simplifier.

simplifier types_ext funcs_ext sfuncs uvars vars rp_v rp_pf sp_v sp_pf rv_v rv_pf st sis is SF evalInstrs_pf sepFormula_pf :=

  intro F.



(*
  Ltac sym_eval simplifier :=
    match goal with
      | [ H : evalInstrs ?stn ?st ?is = None
        , H' : PropX.interp ?cs (SepIL.SepFormula.sepFormula ?SF (?stn, ?st)) |- _ ] =>
        (** Safety **)
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
                    let types_ext := eval simpl in (bedrock_ext types) in 
                    let funcs := eval unfold bedrock_funcs in (bedrock_funcs types_ext) in
                    let funcs := eval simpl in funcs in
                    let sfuncs := constr:(@nil (@SEP.ssignature types pcT stT)) in
                    let uvars := eval simpl in (@nil _ : Expr.env types) in
                    let vars := eval simpl in (@nil _ : Expr.env types) in
                    reflect_instrs ltac:(isConst) is types funcs uvars vars ltac:(fun funcs sis =>
                    SEP.reflect_expr ltac:(isConst) rp_v types funcs uvars vars ltac:(fun funcs rp_v =>
                    SEP.reflect_expr ltac:(isConst) sp_v types funcs uvars vars ltac:(fun funcs sp_v =>
                    SEP.reflect_expr ltac:(isConst) rv_v types funcs uvars vars ltac:(fun funcs rv_v =>
                    SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
                    match funcs with
                      | _ :: _ :: _ :: ?funcs_ext =>
                        build_evals sfuncs types_ext funcs_ext ltac:(fun knowns evals =>
                          generalize (@sym_evalInstrs_safe_apply types_ext funcs_ext sfuncs knowns evals
                            uvars vars cs is stn st H sp_v rv_v rp_v SF H'
                            sp_pf rv_pf rp_pf _ (refl_equal _) sis (refl_equal _)))
                    end)))))
                end
            end
        end;
        let z := fresh in
        intro z ;
        ((simplifier z; evaluator z) || fail 1 "simplification failed!"); try assumption
      
      | [ H : evalInstrs ?stn ?st ?is = Some ?st' 
        , H' : PropX.interp ?cs (SepIL.SepFormula.sepFormula ?SF (?stn, ?st)) |- _ ] =>
        (** Correctness **)
        let doIt rp_v rp_pf sp_v sp_pf rv_v rv_pf st is SF H H' :=
          let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
          let Ts := constr:(@nil Type) in
          let Ts := collectTypes_instrs is Ts in
          let Ts := SEP.collectAllTypes_expr isConst Ts regs in
          let Ts := SEP.collectAllTypes_sexpr isConst Ts (SF :: nil) in
          let types := eval unfold bedrock_types in bedrock_types in
          let types := SEP.extend_all_types Ts types in
          let types_ext := eval simpl in (bedrock_ext types) in
          let funcs := eval unfold bedrock_funcs in (bedrock_funcs types_ext) in
          let funcs := eval simpl in funcs in
          let sfuncs := constr:(@nil (@SEP.ssignature types pcT stT)) in
          let uvars := eval simpl in (@nil _ : Expr.env types) in
          let vars := eval simpl in (@nil _ : Expr.env types) in
          reflect_instrs ltac:(isConst) is types funcs uvars vars ltac:(fun funcs sis =>
          SEP.reflect_expr ltac:(isConst) rp_v types funcs uvars vars ltac:(fun funcs rp_v =>
          SEP.reflect_expr ltac:(isConst) sp_v types funcs uvars vars ltac:(fun funcs sp_v =>
          SEP.reflect_expr ltac:(isConst) rv_v types funcs uvars vars ltac:(fun funcs rv_v =>
          SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
            match funcs with
              | _ :: _ :: _ :: ?funcs_ext =>
                build_evals sfuncs types_ext funcs_ext ltac:(fun knowns evals =>
                  generalize (@sym_evalInstrs_sound_apply types_ext funcs_ext sfuncs knowns evals
                    uvars vars cs is stn st _ H sp_v rv_v rp_v SF H'
                    sp_pf rv_pf rp_pf _ (refl_equal _) sis (refl_equal _)))
            end)))))
        in
        let rec loop :=
          let p := fresh in
          intro p ;
          ((simplifier p; evaluator p) || fail 1 "simplification failed!");
          match goal with 
            | [ p : (_ = ?sp /\ (_ = ?rp /\ _ = ?rv)) /\ interp cs (SepIL.SepFormula.sepFormula ?SF (stn, ?st')) |- _ ] =>
              (** it finished! **)
              match goal with
                | [ H'' : evalInstrs stn st' ?is = Some ?st'' |- _ ] =>
                  (** more to go **)
                  doIt rp (Some_inj (proj1 (proj2 (proj1 p)))) sp (Some_inj (proj1 (proj1 p))) rv (Some_inj (proj2 (proj2 (proj1 p)))) st' is SF H'' (proj2 p);
                  clear p H'' ; loop
                | [ |- _ ] =>
                  destruct p as [ [ ? [ ? ? ] ] ? ]
              end            
            | [ p : exists st'', _ |- _ ] =>
              destruct p as [ ? [ ? ? ] ]
          end
        in
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
            match find_reg st Sp with
              | (?sp_v, ?sp_pf) =>
                match find_reg st Rv with
                  | (?rv_v, ?rv_pf) =>
                    doIt rp_v rp_pf sp_v sp_pf rv_v rv_pf st is SF H H' ; clear H H' ; loop
                end
            end
        end
    end.

  Focus 2.
  

  sym_eval simplifier.

  Check sym_evalInstrs_sound_apply.



  clear H1. clear H0.

  intuition.
  eexists.
  split. rewrite H0. eassumption.
  simpl. ho.

  eexists. rewrite H4. ho. eassumption.
Qed.


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