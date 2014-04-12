(** Compiling the deeply embedded programming language *)

Require Import AutoSep Wrap Malloc.

Require Import Depl.Logic Depl.Cancel Depl.AlgebraicDatatypes Depl.Statements.


(** * Lowering DEPL expressions to Bedrock SPS expressions *)

Definition exprC (e : expr) : rvalue' :=
  match e with
    | Var x => x
    | Const w => w
  end.
(** The above looks like a bit of magic.  It's all in the coercions (from main Bedrock library). *)

Theorem exprC_correct : forall specs P stn st xs V vs fE e e' res fvs,
  vars_ok fE V vs
  -> exprD vs e = Some e'
  -> exprV xs e
  -> ~In "rp" xs
  -> interp specs (![locals ("rp" :: xs) V res (Regs st Sp) * P] (stn, st))
  -> (forall x e0, vs x = Some e0
    -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e0 fE1 = Logic.exprD e0 fE2)
  -> exists w,
    evalRvalue stn st (exprC e xs) = Some w
    /\ Logic.exprD e' fE = Dyn w
    /\ (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e' fE1 = Logic.exprD e' fE2).
Proof.
  destruct e; simpl; intuition.

  injection H0; clear H0; intros; subst; eauto.

  assert (Hnone : evalInstrs stn st (IL.Assign Rv (variableSlot x xs) :: nil) <> None).
  simp.
  generalize dependent H0.
  evaluate auto_ext.

  assert (Hsome : forall st', evalInstrs stn st (IL.Assign Rv (variableSlot x xs) :: nil) = Some st'
    -> Regs st' Rv = sel V x).
  simp.
  generalize dependent H0.
  evaluate auto_ext; auto.

  Transparent evalInstrs.
  simpl in *.
  Opaque evalInstrs.
  match goal with
    | [ |- exists x, ?X = _ /\ _ ] => destruct X; try tauto
  end.
  specialize (Hsome _ eq_refl); simpl in *.
  rewrite rupd_eq in Hsome; subst.
  eauto 10.
Qed.

Theorem exprC_hygienic : forall xs vs e e' fvs,
  exprD vs e = Some e'
  -> exprV xs e
  -> ~In "rp" xs
  -> (forall x e0, vs x = Some e0
    -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e0 fE1 = Logic.exprD e0 fE2)
  -> (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y) -> Logic.exprD e' fE1 = Logic.exprD e' fE2).
Proof.
  destruct e; simpl; intuition eauto.

  injection H; clear H; intros; subst; eauto.
Qed.


(** * Lowering statements *)

Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
  Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).
Local Infix ";;" := SimpleSeq : SP_scope.

Fixpoint locateCon' (n : nat) (s : string) (cs : list ncon) : option (nat * ncon) :=
  match cs with
    | nil => None
    | c :: cs' => if string_eq s (NName c) then Some (n, c)
      else locateCon' (S n) s cs'
  end.

Fixpoint locateCon (s : string) (dts : list ndatatype) : option (string * nat * ncon) :=
  match dts with
    | nil => None
    | dt :: dts' =>
      match locateCon' O s (snd dt) with
        | None => locateCon s dts'
        | Some (n, c) => Some (fst dt, n, c)
      end
  end.

(** Version of [Logic.predD] specialized to predicates with no free higher-order variables *)
Definition predD (p : pred) (fE : fo_env) : HProp :=
  predD p (fun _ _ => Emp)%Sep fE.
Definition normalD (p : normal) (fE : fo_env) : HProp :=
  normalD p (fun _ _ => Emp)%Sep fE.

(** Generic precondition of a statement, translated to base Bedrock from Depl-speak *)
Definition precond (vs : vars) (pre post : normal) :=
  (* First, quantify over a context assigning values to specification variables. *)
  Al fE,
    (* Naturally, we rely on the malloc() data structures being around. *)
    PRE[V] mallocHeap 0
      (* We also need the Depl precondition, of course. *)
      * normalD pre fE
      (* Finally, the symbolic variable valuation should be accurate. *)
      * [| vars_ok fE V vs |]
    POST[R] mallocHeap 0
      (* The postcondition holds, in an [fo_env] that lets it mention the return value. *)
      * normalD post (fo_set fE "result" (Dyn R)).

(** Evaluate the arguments to a constructor, saving results in a record in memory. *)
Fixpoint initArgs (args : list expr) (base : fo_var) (pos : nat) : chunk :=
  match args with
  | nil => Skip
  | arg :: args =>
    base + pos *<- exprC arg;;
    initArgs args base (4 + pos)
  end%SP.

Section ForallF.
  Variable A : Type.
  Variables P Q : A -> Prop.

  Hypothesis P_Q : forall x, P x -> Q x.

  Theorem ForallF_weaken : forall ls,
    ForallF P ls -> ForallF Q ls.
  Proof.
    induction ls; simpl; intuition.
  Qed.
End ForallF.

Section stmtC.
  Variable dts : list ndatatype.

  Fixpoint stmtC (vs : vars) (fvs : list fo_var)
    (pre post : normal) (nextDt : string) (s : stmt)
    (k : vars -> list fo_var -> normal -> normal -> string -> chunk) : chunk :=
    match s with
      | Assign x e =>
        match exprD vs e with
          | None => Fail
          | Some e' => x <- exprC e;; k (vars_set vs x e') fvs pre post nextDt
        end
      | Seq s1 s2 => stmtC vs fvs pre post nextDt s1
        (fun vs' fvs' pre' post' nextDt' =>
          stmtC vs' fvs' pre' post' nextDt' s2 k)
      | Ret e => Return (exprC e)
      | Allocate x conName args =>
        match locateCon conName dts with
          | None => Fail
          | Some (dtName, tag, c) =>
            match exprsD vs args with
              | None => Fail
              | Some args' =>
                match cancel fvs ("this" :: nil)
                  pre (allocatePre dtName c args') with
                  | Failure _ => Fail
                  | Success s lhs P =>
                    match s "this" with
                      | None => Fail
                      | Some model =>
                        let vs' := vars_set vs x (Logic.Var nextDt) in
                        let pre' := {| NQuants := NQuants pre;
                          NPure := NPure pre;
                          NImpure := Named dtName (model :: Logic.Var nextDt
                            :: nil) :: lhs |} in
                        x <-- Call "malloc"!"malloc"(0, S (length args))
                        [precond vs' pre' post];;
                        x *<- tag;;
                        initArgs args x 4;;
                        k vs' (nextDt :: fvs) pre' post (nextDt ++ "'")%string
                    end
                end
            end
        end
    end%SP.


  (** * Key lemmas to pass to Wrap *)

  Lemma vars_ok_sel : forall fE V vs,
    vars_ok fE (sel V) vs = vars_ok fE V vs.
  Proof.
    auto.
  Qed.

  Hint Rewrite vars_ok_sel.

  (* Use a hypothesis telling us an expanded form implied by the known precondition. *)
  Ltac pre_implies :=
    match goal with
      | [ H : interp _ _, H' : forall specs0 : codeSpec _ _, _ |- _ ] =>
        apply H' in H; clear H'; post; intuition idtac; autorewrite with core in *
    end.

  Ltac rewriteall :=
    repeat match goal with
             | [ H : _ |- _ ] => rewrite H in *
           end.

  (* Case-split on an [option] being [match]ed in conclusion. *)
  Ltac case_option :=
    match goal with
      | [ |- context[match ?E with None => _ | _ => _ end] ] =>
        match E with
          | context[match _ with None => _ | _ => _ end] => fail 1
          | _ => case_eq E; post
        end
      | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
        match E with
          | context[match _ with None => _ | _ => _ end] => fail 1
          | _ => case_eq E; post; rewriteall
        end
      | [ _ : context[if in_dec string_dec ?x ?y then _ else _] |- _ ] =>
        destruct (in_dec string_dec x y); post
    end; autorewrite with core in *.

  (* Use a hypothesis about some fact holding for all members of a list. *)
  Ltac use_In :=
    match goal with
      | [ H : forall x, In x ?xs -> _ -> False, H' : In _ ?xs |- _ ] =>
        let T := type of (H _ H') in
          match goal with
            | [ _ : T |- _ ] => fail 1
            | _ => generalize (H _ H'); intro
          end
    end.

  (* Use [evaluate] to get pure facts in a precondition into the normal proof context. *)
  Ltac pre_evalu :=
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => generalize dependent H
             | [ H : _ _ = Some _ |- _ ] => generalize dependent H
             | [ H : _ _ = None -> False |- _ ] => generalize dependent H
             | [ x : _ -> option Logic.expr |- _ ] => change vars in x
             | [ x : vars -> _ |- _ ] => generalize dependent x
             | [ H : importsGlobal _ |- _ ] => generalize dependent H
           end;
    try match goal with
          | [ _ : interp _ (![_] (fst ?st, _)) |- _ ] =>
            destruct st; simpl in *
        end; clear_fancy; evaluate auto_ext; intros.

  (* Clear hypotheses that will confuse Bedrock automation. *)
  Ltac cancl_clear :=
    repeat match goal with
             | [ H : importsGlobal _ |- _ ] => clear dependent H
             | [ H : _ _ = Some _ |- _ ] => clear H
             | [ H : (_ _ <> None)%type |- _ ] => clear H
             | [ H : _ _ = None -> False |- _ ] => clear H
             | [ H : stmtD _ _ _ _ _ |- _ ] => clear H
           end.

  (* Use separation logic entailment from a hypothesis to conclusion. *)
  Ltac cancl :=
    match goal with
      | [ _ : interp ?specs1 (![_] (?s1, ?x1)) |- interp ?specs2 (![_] (?s2, ?x2)) ] =>
        equate specs1 specs2; equate s1 s2; equate x1 x2;
        cancl_clear; cancel auto_ext
      | [ _ : interp ?specs (![_] ?s) |- interp ?specs (![_] ?s) ] =>
        cancl_clear; cancel auto_ext
      | [ |- interp _  (![_]%PropX _ ---> ![_]%PropX _) ] => cancl_clear; cancel auto_ext
    end.

  (* Apply the [exprC_correct] lemma, using cancelation to prove one of its premises. *)
  Ltac exprC_correct :=
    match goal with
      | [ H : exprD _ _ = Some _ |- _ ] => eapply exprC_correct in H; try cancl; eauto;
        try match goal with
              | [ H : exists x, _ /\ _ |- _ ] => destruct H as [ ? [ ? [ ] ] ]
            end
    end.

  Lemma determine_rvalue : forall stn st lv rv st' w is,
    evalInstrs stn st (IL.Assign lv rv :: is) = st'
    -> evalRvalue stn st rv = Some w
    -> evalInstrs stn st (IL.Assign lv w :: is) = st'.
  Proof.
    Transparent evalInstrs.
    simpl; intros.
    rewrite H0 in *; auto.
    Opaque evalInstrs.
  Qed.

  (* Use a previous conclusion of [exprC_correct] to simplify an [evalInstrs] hypothesis. *)
  Ltac determine_rvalue :=
    match goal with
      | [ H1 : evalInstrs _ _ _ = _, H2 : evalRvalue _ _ _ = Some _ |- _ ] =>
        eapply determine_rvalue in H1; [ clear H2 | exact H2 ]
    end.

  (* Full symbolic evaluation *)
  Ltac evalu :=
    try determine_rvalue;
      try match goal with
            | [ H : In _ _, H' : forall x, In x _ -> In x _ |- _ ] =>
              apply H' in H
          end; simp;
      repeat match goal with
               | [ H : _ _ = Some _ |- _ ] => generalize dependent H
               | [ H : _ _ = None -> False |- _ ] => generalize dependent H
               | [ H : importsGlobal _ |- _ ] => generalize dependent H
             end; clear_fancy;
    (* Extra simplification for function return *)
    try match goal with
          | [ _ : context[locals ("rp" :: ?ns) _ _ _], H : context[natToW 0] |- _ ] =>
            assert (In "rp" ("rp" :: ns)) by (simpl; tauto);
              change (natToW 0) with (natToW (variablePosition ("rp" :: ns) "rp")) in H
        end;
    evaluate auto_ext; intros.

  Ltac my_descend := descend; autorewrite with core in *.
  Hint Rewrite sel_upd_ne using (intro; subst; tauto).

  Lemma string_eq_complete : forall s1 s2,
    if string_eq s1 s2 then s1 = s2 else s1 <> s2.
  Proof.
    intros; destruct (string_dec s1 s2); subst.
    rewrite string_eq_true; auto.
    rewrite string_eq_false; auto.
  Qed.

  Lemma vars_ok_upd : forall fE V vs x w e,
    vars_ok fE V vs
    -> Logic.exprD e fE = Dyn w
    -> vars_ok fE (upd V x w) (vars_set vs x e).
  Proof.
    unfold vars_ok, sel, upd, vars_set; intros.
    generalize (string_eq_complete x0 x).
    destruct (string_eq x0 x), (string_dec x0 x); intuition.
  Qed.

  Local Hint Resolve vars_ok_upd.

  Lemma exprV_weaken : forall xs xs',
    (forall x, In x xs -> In x xs')
    -> forall e, exprV xs e -> exprV xs' e.
  Proof.
    destruct e; simpl; intuition.
  Qed.

  Local Hint Resolve exprV_weaken.

  Lemma stmtV_weaken : forall xs xs',
    (forall x, In x xs -> In x xs')
    -> forall s, stmtV dts xs s -> stmtV dts xs' s.
  Proof.
    induction s; simpl; intuition eauto using ForallF_weaken.
  Qed.

  Local Hint Resolve stmtV_weaken.

  Lemma vars_set_contra : forall vs x v x' v',
    vars_set vs x v x' = None
    -> vs x = Some v'
    -> (vs x' = None -> False)
    -> False.
  Proof.
    unfold vars_set; intros;
      destruct (string_dec x' x); subst; eauto; discriminate.
  Qed.

  Local Hint Resolve vars_set_contra.

  (* VC generation uses some empty marker predicates to indicate failure.
   * Try to find one to invert on, proving the goal trivially. *)
  Ltac use_error_message :=
    match goal with
      | [ H : bad_assignment_lhs _ |- _ ] => inversion H
      | [ H : bad_assignment_rhs _ |- _ ] => inversion H
    end.

  (* Use the induction hypotheses (recursively) in the proof below. *)
  Ltac Stmt_use_IH' :=
    eauto; repeat post; my_descend; post; my_descend;
      repeat (my_descend; cancl || (step auto_ext; my_descend)).

  Ltac Stmt_use_IH :=
    match goal with
      | [ IH : forall pre0 : _ -> _, _, H : interp _ (Structured.Postcondition _ _) |- _ ] =>
        eapply IH in H; clear IH; auto;
          try match goal with
                | [ |- forall specs : codeSpec _ _, _ ] => intros; Stmt_use_IH
              end; Stmt_use_IH'
    end.

  Lemma addQuants_Emp : forall G (S : subs _ _ G) qs fE,
    SubstsH S (addQuants qs (fun _ : fo_env => Emp) fE) ===> Emp.
  Proof.
    induction qs; simpl; intros; Himp.

    apply Himp_refl.

    apply Himp'_ex; auto.
  Qed.

  Theorem sentail_sound : forall fvs fE S lhs rhs P,
    sentail fvs lhs rhs = ProveThis P
    -> P
    -> List.Forall (wellScoped (NQuants rhs ++ fvs)) (NImpure rhs)
    -> (forall x, In x fvs -> ~In x (NQuants lhs))
    -> SubstsH S (normalD lhs fE)
    ===> SubstsH S (normalD rhs fE).
  Proof.
    unfold sentail; intros.
    case_eq (cancel fvs nil lhs rhs); intros.
    Focus 2.
    rewrite H3 in *; discriminate.
    rewrite H3 in *.
    destruct NewLhs; try discriminate.
    injection H; clear H; intros; subst.
    assert (Heasy : forall x, In x fvs -> ~In x nil) by (simpl; tauto).
    specialize (cancel_sound fvs nil fE nil (fun _ _ => Emp%Sep) S _ _ _ _ _ Heasy H3 H0 H1).
    unfold Logic.normalD at 3; simpl.
    intros.
    unfold normalD.
    eapply Himp_trans; try apply H; clear H; auto.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | ] | ].
    apply addQuants_Emp.
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_Emp.
  Qed.

  Lemma use_hygiene : forall fvs vs x x' e0 e2 fE1 fE2,
    (forall x e, vs x = Some e
      -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
        -> Logic.exprD e fE1 = Logic.exprD e fE2)
    -> (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
      -> Logic.exprD e0 fE1 = Logic.exprD e0 fE2)
    -> vars_set vs x e0 x' = Some e2
    -> (forall y, In y fvs -> fE1 y = fE2 y)
    -> Logic.exprD e2 fE1 = Logic.exprD e2 fE2.
  Proof.
    unfold vars_set; intros.
    destruct (string_dec x' x); subst; eauto.
    injection H1; clear H1; intros; subst; eauto.
  Qed.

  Hint Immediate use_hygiene.

  (* Prove we never run off the end of a function.
   * We're in CPS, so all postconditions should be contradictory. *)
  Theorem stmtC_post : forall im mn (H : importsGlobal im) ns res s k,
    (forall specs st vs fvs pre post nextDt pre0,
       interp specs (Structured.Postcondition (toCmd (k vs fvs pre post nextDt)
                                                     mn H ns res pre0) st)
       -> False)
    -> (forall specs st vs fvs pre post nextDt pre0,
       interp specs (Structured.Postcondition (toCmd (stmtC vs fvs pre post nextDt s k)
                                                     mn H ns res pre0) st)
       -> False).
  Proof.
    induction s; simpl; intuition idtac;
      repeat match goal with
               | [ _ : context[match ?E with _ => _ end] |- _ ] =>
                 destruct E; simpl in *; eauto
               | [ IH : forall k : _ -> _, _, H : interp _ (Structured.Postcondition _ _) |- _ ] =>
                 apply IH in H; clear IH; intuition idtac
               | [ H : interp _ [| False |]%PropX |- _ ] => propxFo
               | [ x : (_ * _)%type |- _ ] => destruct x
             end.
  Qed.

  Definition normalWf' := normalWf.

  Definition scopey fvs post := List.Forall (wellScoped (NQuants post ++ "result" :: fvs)).
  Definition scopey' x := List.Forall (fun p => exists bvs, boundVars p = Some bvs /\ ~In x bvs).

  Theorem nsubst_bwd : forall x e fvs n fE,
    normalWf fvs n
    -> fE x = Logic.exprD e fE
    -> (forall y, In y fvs -> ~In y (NQuants n))
    -> (forall fE1 fE2, (forall x, In x fvs -> fE1 x = fE2 x)
      -> Logic.exprD e fE1 = Logic.exprD e fE2)
    -> In x fvs
    -> normalD (nsubst x e n) fE ===> normalD n fE.
  Proof.
    intros.
    change (normalD (nsubst x e n) fE) with (SubstsH (SNil _ _) (normalD (nsubst x e n) fE)).
    change (normalD n fE) with (SubstsH (SNil _ _) (normalD n fE)).
    eapply nsubst_bwd; eauto.
  Qed.

  Lemma stmtC_vc : forall im mn (H : importsGlobal im) ns res xs
    (Hres : (res >= 3)%nat),
    ~In "rp" ns
    -> (forall x, In x xs -> In x ns)
    -> forall s vs fvs pre post nextDt kC pre0 kD,
      ~In "result" fvs
      -> normalWf' fvs pre
      -> normalWf' ("result" :: fvs) post
      -> ~In "result" (NQuants pre)
      -> ~In "result" (NQuants post)
      -> scopey fvs post (NImpure post)
      -> scopey' "result" (NImpure pre)
      -> (forall x, In x fvs -> ~In x (NQuants pre))
      -> (forall x, In x fvs -> ~In x (NQuants post))
      -> stmtD dts xs vs fvs pre post nextDt s kD
      -> (forall x e, vs x = Some e
        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
          -> Logic.exprD e fE1 = Logic.exprD e fE2)
      -> (forall specs st,
        interp specs (pre0 st)
        -> interp specs (precond vs pre post true (fun x => x) ns res st))
      -> (forall vs fvs pre post nextDt pre0,
        kD vs fvs pre post nextDt
        -> ~In "result" fvs
        -> normalWf' fvs pre
        -> normalWf' ("result" :: fvs) post
        -> ~In "result" (NQuants pre)
        -> ~In "result" (NQuants post)
        -> scopey fvs post (NImpure post)
        -> scopey' "result" (NImpure pre)
        -> (forall x, In x fvs -> ~In x (NQuants pre))
        -> (forall x, In x fvs -> ~In x (NQuants post))
        -> (forall x e, vs x = Some e
          -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
            -> Logic.exprD e fE1 = Logic.exprD e fE2)
        -> (forall specs st,
          interp specs (pre0 st)
          -> interp specs (precond vs pre post true (fun x => x) ns res st))
        -> vcs (VerifCond (toCmd (kC vs fvs pre post nextDt) mn H ns res pre0)))
      -> stmtV dts xs s
      -> vcs (VerifCond (toCmd (stmtC vs fvs pre post nextDt s kC) mn H ns res pre0)).
  Proof.
    induction s.

    (* Assign *)
    wrap0.
    simpl in *; intuition idtac.
    case_option.
    wrap0.
    pre_implies.
    simpl in *; intuition eauto.
    pre_evalu.
    exprC_correct.
    evalu.
    rewriteall.
    case_option.
    apply H14; intuition idtac.
    unfold vars_set in H18.
    destruct (string_dec x0 x); subst.
    injection H18; clear H18; intros; subst; eauto.
    eauto using exprC_hygienic.
    eauto.
    propxFo.
    pre_implies.
    pre_evalu.
    exprC_correct.
    evalu.
    descend.
    rewrite vars_ok_sel.
    cancl_clear.
    step auto_ext.
    descend; step auto_ext.
    cancl_clear.
    descend; step auto_ext.
    descend; step auto_ext.
    descend; step auto_ext.
    descend; step auto_ext.
    rewriteall.
    use_error_message.

    (* Sequence *)
    wrap0.
    simpl in *; intuition idtac.
    eapply IHs1; intuition eauto.

    (* Return *)
    wrap0.
    pre_implies.
    case_option; simpl in *; intuition eauto.
    pre_evalu.
    exprC_correct.
    evalu.

    pre_implies.
    case_option; simpl in *; intuition eauto.
    pre_evalu.
    exprC_correct.
    evalu.
    case_eq (sentail fvs pre (nsubst "result" e0 post)); intros.
    Focus 2.
    rewrite H25 in *; inversion H11.
    rewrite H25 in *.
    descend.
    step auto_ext.
    step auto_ext.
    descend.
    cancl.
    specialize (sentail_sound fvs (fo_set x0 "result" (Dyn (Regs st Rv))) (@SNil _ _) _ _ _ H25); intuition.
    unfold SubstsH in *; simpl in *.
    eapply Himp_trans; [ | eapply nsubst_bwd; eauto ].
    eapply Himp_trans; [ | apply H22 ].

    eapply weaken_normalD; eauto.
    intros.
    unfold fo_set.
    destruct (string_dec x4 "result"); subst; tauto.
    2: eauto.
    3: simpl; unfold not; intuition (subst; eauto).
    4: simpl; tauto.

    Focus 2.
    unfold fo_set at 1; simpl.
    etransitivity; try (symmetry; apply H20).
    apply H21.
    unfold fo_set; intros.
    destruct (string_dec y "result"); subst; eauto; exfalso; eauto.

    2: simpl; eauto.

    eapply Forall_forall; intros.
    eapply in_map_iff in H16; destruct H16; intuition subst.
    eapply Forall_forall in H24; try apply H7.

    eapply wellScoped_psubst.
    eapply wellScoped_weaken; eauto.
    simpl; intuition idtac.
    apply in_app_or in H; intuition eauto using in_or_app.
    simpl in *; intuition eauto using in_or_app.
    eauto using in_or_app.

    (* Allocate *)
    wrap0.
    simpl in *; intuition idtac.

    Lemma lookupCon'_locateCon' : forall nm dts0 n,
      match lookupCon' nm dts0 with
        | Some c => exists tag, locateCon' n nm dts0 = Some (tag, c)
        | None => locateCon' n nm dts0 = None
      end.
    Proof.
      induction dts0; simpl; intuition.
      destruct (string_eq nm (NName a)); subst; eauto.
      apply IHdts0.
    Qed.

    Lemma lookupCon_locateCon : forall nm dtName c dts0,
      lookupCon nm dts0 = Some (dtName, c)
      -> exists tag, locateCon nm dts0 = Some (dtName, tag, c).
    Proof.
      induction dts0; simpl; intuition.
      specialize (lookupCon'_locateCon' nm (snd a) 0).
      destruct (lookupCon' nm (snd a)); firstorder.
      injection H; clear H; intros; subst.
      rewrite H0; eauto.
      rewrite H0; eauto.
    Qed.

    case_eq (lookupCon conName dts); intros.
    2: rewrite H17 in *; inversion H11.
    rewrite H17 in *.
    destruct p; simpl in *.
    destruct (lookupCon_locateCon _ _ _ _ H17).
    rewrite H19.
    case_eq (exprsD vs args); intros.
    2: rewrite H20 in *; inversion H11.
    rewrite H20 in *.
    case_eq (cancel fvs ("this" :: nil) pre (allocatePre s n l)); intros.
    2: rewrite H21 in *; inversion H11.
    rewrite H21 in *.
    case_eq (NewSub "this"); intros.
    2: rewrite H22 in *; inversion H11.
    rewrite H22 in *.
    destruct (in_dec string_dec nextDt fvs); try solve [ inversion H11 ].
    Opaque mult.
    wrap0.

    pre_implies.
    clear H21 H15 H18.
    pre_evalu.
    change (locals ("rp" :: ns) x3 res (Regs st Sp))
      with (locals_call ("rp" :: ns) x3 res (Regs st Sp) ("rp" :: "base" :: "n" :: nil) (res - 3) (S (S (S (S 4 * length ns))))) in H14.
    assert (ok_call ("rp" :: ns) ("rp" :: "base" :: "n" :: nil) res (res - 3)
      (S (S (S (S (4 * length ns))))))
    by (split; [ simpl; omega
      | split; [ simpl; omega
        | split; [ NoDup
          | simpl; omega ] ] ] ).
    replace (4 * S (length ns)) with (S (S (S (S (4 * length ns))))) in H15 by omega.
    evalu.

    admit.
    admit.
    admit.
    admit.
    admit.
  Qed.
End stmtC.


Local Hint Immediate wellScoped_predExt.

Lemma scopey_normalize : forall fvs post post' bvs',
  wellScoped ("result" :: fvs) post
  -> boundVars post = Some bvs'
  -> (forall x, In x bvs' -> ~In x ("result" :: fvs))
  -> post' = normalize post
  -> scopey fvs post' (NImpure post').
Proof.
  intros; subst.
  eapply normalize_wf in H0; eauto; intuition.
Qed.

Local Hint Immediate scopey_normalize.
Local Hint Resolve normalize_boundVars.

Lemma normalize_NImpure_keeps : forall p fvs bvs,
  wellScoped fvs p
  -> boundVars p = Some bvs
  -> (forall x, In x bvs -> ~In x fvs)
  -> ~In "result" bvs
  -> scopey' "result" (NImpure (normalize p)).
Proof.
  unfold scopey'; induction p; simpl; intuition eauto.

  caser.
  apply Forall_app; eauto 10 using in_or_app.

  caser.
  eapply IHp.
  eauto.
  eauto.
  2: eauto.
  simpl; intuition (subst; eauto using In_notInList).
Qed.

Local Hint Immediate normalize_NImpure_keeps.

(** Main statement compiler/combinator/macro *)
Definition Stmt
  (dts : list datatype)
  (* Available algebraic datatypes *)
  (fvs : list fo_var)
  (* Logical variables available to mention *)
  (bvs bvs' : list fo_var)
  (* Logical variables bound within [pre] and [post] *)
  (xs : list pr_var)
  (* Program variables available to mention *)
  (vs : vars)
  (* Symbolic valuation to those variables *)
  (pre post : pred)
  (* The Depl-level separation-logic specification for this statement *)
  (s : stmt)
  (* The statement to compile *)
  : chunk.
Proof.
  pose (dts' := map normalizeDatatype dts).
  pose (pre' := normalize pre).
  pose (post' := normalize post).
  apply (WrapC (stmtC dts' vs fvs pre' post' "D" s (fun _ _ _ _ _ => Fail))
    (precond vs pre' post')
    (fun _ _ _ _ _ => [| False |])%PropX
    (* Unsatisfiable postcondition, since we won't allow running off the end of
     * a function body without returning *)

    (* VERIFICATION CONDITION *)
    (fun _ ns res =>
      incl xs ns
      :: (~In "rp" ns)
      :: stmtV dts' xs s
      :: (forall x e, vs x = Some e
        -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
          -> Logic.exprD e fE1 = Logic.exprD e fE2)
      :: wellScoped fvs pre
      :: wellScoped ("result" :: fvs) post
      :: (boundVars pre = Some bvs)
      :: (boundVars post = Some bvs')
      :: (forall x, In x bvs -> ~In x fvs)
      :: (forall x, In x bvs' -> ~In x ("result" :: fvs))
      :: (~In "result" fvs)
      :: (~In "result" bvs)
      :: (~In "result" bvs')
      :: stmtD dts' xs vs fvs pre' post' "D" s (fun _ _ _ _ _ => False)
      :: (res >= 3)%nat
      :: nil)); [
        abstract (wrap0; match goal with
                           | [ H : interp _ _ |- _ ] => eapply stmtC_post in H; eauto; repeat (post; eauto 6)
                         end; post)
        | abstract (wrap0; match goal with
                             | [ H : wellScoped _ _ |- _ ] =>
                               solve [ eapply stmtC_vc; [ | | | | eapply normalize_wf; try apply H; eauto 2
                                 | eapply normalize_wf; eauto
                                 | .. ];
                               unfold pre', post'; eauto 6; cbv beta; tauto ]
                           end) ].
Defined.
