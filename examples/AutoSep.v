Require Import Bedrock.

Set Implicit Arguments.

(** * Let's read from memory! *)

Import SepTac.BedrockEvaluator.
Require Import Bedrock.sep.PtsTo.

Module PLUGIN_PTSTO := BedrockPtsToEvaluator SepTac.PLUGIN.

Definition readS : assert := st ~> ExX, Ex v, ![ $0 =*> v * #0 ] st
  /\ st#Rp @@ (st' ~> [| st'#Rv = v |] /\ ![ $0 =*> v * #1 ] st').

Definition read := bmodule "read" {{
  bfunction "read" [readS] {
    Rv <- $[0];;
    If (Rv = 0) {
      $[0] <- Rv 
    } else {
      $[0] <- Rv
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
Implicit Arguments SEP.sexprD [ types funcs pcType stateType sfuncs ].

Existing Instance PLUGIN_PTSTO.SymEval_ptsto32.
Ltac simplifier H := 
  cbv beta delta [
    PLUGIN_PTSTO.SymEval_ptsto32 PLUGIN_PTSTO.sym_read_word_ptsto32 PLUGIN_PTSTO.sym_write_word_ptsto32
    PLUGIN_PTSTO.expr_equal PLUGIN_PTSTO.types
  ] in H.

Ltac denote_evaluator H :=
     cbv beta iota zeta delta
      [ stateD 
        Expr.exprD
        EquivDec.equiv_dec Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
        eq_rec_r eq_rec eq_rect eq_sym Logic.eq_sym
        funcs
        Expr.Range Expr.Domain Expr.Denotation Expr.tvarD Expr.applyD
        SEP.starred
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

  Ltac sym_eval isConst Ts Fs SFs simplifier :=
    (** NOTE: This has two continuation for success and failure.
     ** success :: stateD_pf rws -> ...
     ** failure :: st stateD_pf rem_pf rws -> ...
     **)
    let rec symeval types_ext funcs_ext sfuncs knowns evals uvars vars 
      sis stateD_pf success failure :=
      let rec continue sis stateD_pf rws :=
        idtac "continue" ;
        match sis with
          | tt => success stateD_pf rws
          | ((?is, ?sis, ?evalInstrs_pf), ?rem) =>
            idtac "apply";
            apply (@sym_evalInstrs_any_apply' types_ext funcs_ext sfuncs knowns evals
              uvars vars (* cs *) _ (* stn *) _ _ _ stateD_pf sis) in evalInstrs_pf ;
            idtac "done apply" ;
            ((simplifier evalInstrs_pf ; sym_evaluator evalInstrs_pf) || fail 100 "simplification failed") ;
            let k := type of evalInstrs_pf in
            match k with
              | False => exfalso; exact evalInstrs_pf
              | @stateD _ _ _ _ _ _ _ _ _ (*(@Build_SymState _ ?M (?ssp, ?srp, ?srv))*) =>
                let rws := constr:((evalInstrs_pf, rws)) in
                continue rem evalInstrs_pf rws
              | exists st'', _ =>
                let a := fresh in
                let b := fresh in
                let c := fresh in 
                destruct evalInstrs_pf as [ a [ b c ] ] ;
                failure a b c rws
            end
        end
      in
      continue sis stateD_pf tt
    in
    let rec get_instrs st :=
      match goal with
        | [ H : evalInstrs _ st ?is = Some ?X |- _ ] =>
          let v := get_instrs X in
          constr:(((is, H), v))
        | [ H : evalInstrs _ st ?is = None |- _ ] =>
          constr:(((is, H), tt))
        | [ |- _ ] => tt
      end
    in
    let rec collectAllTypes_instrs is Ts :=
      match is with
        | tt => Ts
        | ((?i, _), ?is) =>
          let Ts := collectTypes_instrs ltac:(isConst) i Ts in
          collectAllTypes_instrs is Ts
      end
    in
    let rec reflect_all_instrs ais types funcs uvars vars k :=
      match ais with
        | tt => k funcs tt
        | ((?is, ?H), ?ais) =>
          reflect_instrs ltac:(isConst) is types funcs uvars vars ltac:(fun funcs sis =>
            let res := constr:((is, sis, H)) in
            reflect_all_instrs ais types funcs uvars vars ltac:(fun funcs sis => 
              let res := constr:((res, sis)) in
              k funcs res))
      end
    in
    let shouldReflect P :=
      match P with
        | evalInstrs _ _ _ = _ => false
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
    let sheap_simplifier H := 
      cbv iota zeta beta delta 
        [ SEP.star_SHeap SepExpr.FM.add SepExpr.FM.empty SEP.liftSHeap 
          SEP.multimap_join
          SepExpr.other SepExpr.pures SepExpr.impures SepExpr.FM.find
          SepExpr.FM.fold SepExpr.FM.map
          Compare_dec.lt_eq_lt_dec nat_rec nat_rect
          app map
        ] in H
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
                    let all_instrs := get_instrs st in
                    let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
                    (** collect the raw types **)
                    let Ts := collectAllTypes_instrs all_instrs Ts in
                    let Ts := SEP.collectAllTypes_expr ltac:(isConst) Ts regs in
                    let Ts := SEP.collectAllTypes_sexpr isConst Ts (SF :: nil) in
                    let Ts := SEP.collectAllTypes_funcs Ts Fs in
                    let Ts := SEP.collectAllTypes_sfuncs Ts SFs in
                    let Ts := SEP.collectAllTypes_props shouldReflect isConst Ts in
                    (** check for potential universe problems **)
                    match Ts with
                      | context [ PropX.PropX ] => 
                        fail 1000 "found PropX in types list" Ts
                          "(this causes universe inconsistencies)"
                      | context [ PropX.spec ] => 
                        fail 1000 "found PropX in types list" Ts
                          "(this causes universe inconsistencies)"
                      | context [ PropX.spec ] => 
                        fail 1000 "found PropX in types list" Ts
                          "(this causes universe inconsistencies)"
                      | _ => idtac
                    end;
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
                    reflect_all_instrs all_instrs types funcs uvars vars ltac:(fun funcs sis =>
                    SEP.reflect_props shouldReflect ltac:(isConst) types funcs uvars vars ltac:(fun funcs pures proofs =>
                    SEP.reflect_expr ltac:(isConst) rp_v types funcs uvars vars ltac:(fun funcs rp_v =>
                    SEP.reflect_expr ltac:(isConst) sp_v types funcs uvars vars ltac:(fun funcs sp_v =>
                    SEP.reflect_expr ltac:(isConst) rv_v types funcs uvars vars ltac:(fun funcs rv_v =>
                    SEP.reflect_sexpr ltac:(isConst) SF types funcs pcT stT sfuncs uvars vars ltac:(fun funcs sfuncs SF =>
                      match funcs with 
                        | _ :: _ :: _ :: ?funcs_ext =>
                          apply (@stateD_proof types_ext funcs_ext sfuncs uvars vars _ 
                            sp_v rv_v rp_v sp_pf rv_pf rp_pf _ cs stn SF (refl_equal _)) in H' ;
                          sheap_simplifier H' ;
                          build_evals sfuncs types_ext funcs_ext ltac:(fun knowns evals =>
                            symeval types_ext funcs_ext sfuncs knowns evals uvars vars sis H'
                              ltac:(fun stateD_pf rws => 
                                idtac "success" ;
                                simple apply stateD_regs in H' ;
                                denote_evaluator H' ;
                                (try rewrite <- (proj1 H') in * ) ;
                                (try rewrite <- (proj2 (proj2 H')) in * ) ;
                                (try rewrite <- (proj1 (proj2 H')) in * ) ; 
                                let rec rewrite_regs rws :=
                                  match rws with
                                    | tt => idtac
                                    | (?H, tt) => 
                                      denote_evaluator H; destruct H
                                    | (?H, ?rws) =>
                                      rewrite_regs rws ;
                                      denote_evaluator H ; apply proj1 in H ;
                                      (try rewrite <- (proj1 H) in * ) ;
                                      (try rewrite <- (proj2 (proj2 H)) in * ) ;
                                      (try rewrite <- (proj1 (proj2 H)) in * ) ; 
                                      clear H
                                  end
                                in
                                idtac "begin rewriting!" ;
                                rewrite_regs rws; 
                                idtac "end rewriting!";
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
                                end ;
                                idtac "done rewriting")
                              ltac:(fun st stateD_pf rem rws => idtac "failure"))
                      end))))))
                end
            end
        end
    end.

Theorem readOk : moduleOk read.
  structured_auto; autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *;

  sym_eval ltac:(isConst) tt tt tt simplifier.
  admit. admit.
Qed.

(*
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