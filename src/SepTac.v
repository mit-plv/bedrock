Require Import IL SepIL SymIL.
Require Import Word Memory.
Import List.
Require Import DepList EqdepClass.

Require Expr SepExpr.
Module SEP := SymIL.BedrockEvaluator.SEP.
(* (Provers.transitivityEqProverRec funcs) *)
Lemma ApplyCancelSep : forall types hyps funcs eq_prover sfuncs (l r : SEP.sexpr (bedrock_types ++ types) (Expr.tvType O) (Expr.tvType 1)),
  Expr.AllProvable funcs nil nil hyps ->
  forall cs, 
  match SEP.CancelSep (funcs := funcs) eq_prover  hyps l r with
    | {| SEP.vars := vars; 
         SEP.lhs := lhs; SEP.rhs_ex := rhs_ex; 
         SEP.rhs := rhs; SEP.SUBST := SUBST |} =>
      SEP.forallEach vars
        (fun VS : Expr.env (bedrock_types ++ types) =>
          SEP.exists_subst funcs VS
          (ExprUnify.env_of_Subst SUBST rhs_ex 0)
          (fun rhs_ex0 : Expr.env (bedrock_types ++ types) =>
            SEP.himp funcs sfuncs nil rhs_ex0 VS cs lhs rhs))
  end ->
  himp cs (@SEP.sexprD _ funcs _ _ sfuncs nil nil l)
          (@SEP.sexprD _ funcs _ _ sfuncs nil nil r).
Proof.
  unfold Himp. intros. 
  apply SEP.ApplyCancelSep in H0. unfold SEP.himp in *. assumption.
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

Require Import PropX.

Lemma pick_cont : forall specs P Q R CPTR stn_st,
  interp specs (![ P ] stn_st)->
  specs CPTR = Some (fun x => R x) ->
  (forall x, interp specs (Q x ---> R x)) ->
  forall CPTR',
  CPTR = CPTR' ->
  interp specs (Q stn_st) ->
  exists pre', specs CPTR' = Some pre' /\ interp specs (pre' stn_st).
Proof. 
  intros; subst; do 2 esplit; try eassumption.
  eapply Imply_E; eauto.
Qed.

Ltac pick_continuation tac :=
  match goal with
    | [ H : interp ?specs (![ ?P ] ?X)
      , H' : ?specs ?CPTR = Some (fun x => ?R x)
      , H'' : forall x, interp ?specs (@?Q x ---> ?R x)%PropX
      |- exists pre', ?specs ?CPTR' = Some pre' /\ interp _ (pre' ?X) ] =>
    apply (@pick_cont specs P Q R CPTR X H H' H'' CPTR'); 
      [ solve [ tac ]
      | PropXTac.propxFo ; autorewrite with sepFormula ; 
        unfold substH ; simpl subst ]
  end.

Lemma interp_interp_himp : forall cs P Q stn_st,
  interp cs (![ P ] stn_st) ->
  (himp cs P Q) ->
  interp cs (![ Q ] stn_st).
Proof.
  unfold himp. intros. destruct stn_st.
  rewrite sepFormula_eq in *. unfold sepFormula_def in *. simpl in *.
  eapply Imply_E; eauto. 
Qed.

Ltac change_to_himp := 
  match goal with
    | [ H : interp ?specs (![ _ ] ?X)
      |- interp ?specs (![ _ ] ?X) ] =>
    eapply (@interp_interp_himp _ _ _ _ H)
  end.

Ltac sep_canceler isConst prover simplifier Ts :=
  (try change_to_himp) ;
  match goal with 
    | [ |- himp ?cs ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
      let all_props := Expr.collect_props ltac:(fun _ => true) in
      let pures := Expr.props_types all_props in
      let L := eval unfold starB exB hvarB in L in
      let R := eval unfold starB exB hvarB in R in
      (** collect types **)
      let Ts := 
        match Ts with
          | tt => constr:(@nil Type) 
          | _ => Ts
        end
      in
      let Ts := Expr.collectTypes_exprs ltac:(isConst) pures Ts in
      SEP.collectTypes_sexpr ltac:(isConst) L Ts ltac:(fun Ts =>
      SEP.collectTypes_sexpr ltac:(isConst) R Ts ltac:(fun Ts =>
      (** check for potential universe inconsistencies **)
      match Ts with
        | context [ PropX.PropX ] => 
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)"
        | context [ PropX.spec ] => 
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)"
        | _ => idtac
      end ;
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
      (** build the funcs **)
      let funcs := eval unfold SymIL.BedrockEvaluator.bedrock_funcs in (SymIL.BedrockEvaluator.bedrock_funcs types_extV) in
      let funcs := eval simpl in funcs in
      let pcT := constr:(SymIL.BedrockEvaluator.pcT) in
      let stT := constr:(SymIL.BedrockEvaluator.stT) in
      (** build the base sfunctions **)
      let sfuncs := constr:(@nil (@SEP.ssignature typesV pcT stT)) in
      Expr.reflect_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
        let proofs := Expr.props_proof all_props in
      SEP.reflect_sexpr ltac:(isConst) L typesV funcs pcT stT sfuncs uvars vars ltac:(fun uvars funcs sfuncs L =>
      SEP.reflect_sexpr ltac:(isConst) R typesV funcs pcT stT sfuncs uvars vars ltac:(fun uvars funcs sfuncs R =>
        apply (@ApplyCancelSep (SymIL.bedrock_ext typesV) pures funcs 
          (prover _ funcs) sfuncs L R proofs) ;
        unfold typesV, types_extV ;        
        simplifier ;  try reflexivity )))))
  end.

Ltac cancel_simplifier :=
  cbv beta iota zeta delta 
      [ SEP.CancelSep
        SEP.hash SEP.hash' SEP.sepCancel

        SepExpr.FM.fold

        Provers.eq_summary Provers.eq_summarize Provers.eq_prove 
        Provers.transitivityEqProverRec

        ExprUnify.Subst

        SymIL.bedrock_types SymIL.bedrock_ext
        app map fold_right nth_error value error

        fst snd

        SepExpr.impures SEP.star_SHeap SepExpr.FM.empty SEP.liftSHeap
        SEP.sheapSubstU ExprUnify.empty_Subst

        SepExpr.pures SepExpr.impures SepExpr.other

        SEP.exists_subst ExprUnify.env_of_Subst

        SEP.multimap_join SepExpr.FM.add SepExpr.FM.find SepExpr.FM.map

        SEP.unify_remove_all SEP.unify_remove

        SEP.unifyArgs
        ExprUnify.fold_left_2_opt
        Compare_dec.lt_eq_lt_dec nat_rec nat_rect 

        ExprUnify.exprUnify SEP.substV length
        Expr.liftExpr Expr.exprSubstU
        Peano_dec.eq_nat_dec EquivDec.equiv_dec 
        Expr.EqDec_tvar
        Expr.tvar_rec Expr.tvar_rect
        sumbool_rec sumbool_rect
        eq_rec_r eq_rect eq_rec f_equal eq_sym
        ExprUnify.get_Eq
        Expr.Eq
        EquivDec.nat_eq_eqdec
        Provers.inSameGroup Provers.eqD Provers.eqD_seq Provers.transitivityEqProver
        Provers.groupsOf
        Provers.addEquality
        Provers.in_seq_dec
        Expr.typeof 
        Expr.expr_seq_dec
        Expr.tvarD
        Expr.tvar_val_sdec 
        Provers.groupWith
        Expr.Range Expr.Domain Expr.Denotation
        Expr.well_typed 
        Expr.all2

        SEP.forallEach
        SEP.sheapD SEP.sexprD
        SEP.starred SEP.himp
        Expr.Impl Expr.is_well_typed
      ].

(*
Require Unfolder.
Module U := Unfolder.Make BedrockHeap ST.
*)

Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).
