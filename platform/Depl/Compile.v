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


(** * Lowering statements *)

Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
  Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).
Local Infix ";;" := SimpleSeq : SP_scope.

Fixpoint stmtC (s : stmt) : chunk :=
  match s with
    | Assign x e => x <- exprC e
    | Seq s1 s2 => stmtC s1;; stmtC s2
    | Ret e => Return (exprC e)
  end%SP.

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
  -> forall s, stmtV xs s -> stmtV xs' s.
Proof.
  induction s; simpl; intuition eauto.
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
  case_eq (cancel fvs lhs rhs); intros.
  Focus 2.
  rewrite H3 in *; discriminate.
  rewrite H3 in *.
  destruct NewLhs; try discriminate.
  injection H; clear H; intros; subst.
  specialize (cancel_sound fvs fE nil (fun _ _ => Emp%Sep) S _ _ _ _ H3 H0 H1).
  unfold Logic.normalD at 3; simpl.
  intros.
  unfold normalD.
  eapply Himp_trans; try apply H; clear H; auto.
  eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | ] | ].
  apply addQuants_Emp.
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_Emp.
Qed.

Section fvs.
  Variable fvs : list fo_var.

  Lemma use_hygiene : forall vs x x' e0 e2 fE1 fE2,
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

  Lemma Stmt_post : forall pre post im mn (H : importsGlobal im) ns res xs,
    ~In "rp" ns
    -> (forall x, In x xs -> In x ns)
    -> forall s pre0 k,
      (forall specs st,
        interp specs (pre0 st)
        -> exists vs, interp specs (precond vs pre post true (fun x => x) ns res st)
          /\ stmtD pre post fvs vs s k
          /\ (forall x e, vs x = Some e
            -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
              -> Logic.exprD e fE1 = Logic.exprD e fE2))
      -> stmtV xs s
      -> forall specs st, interp specs (Structured.Postcondition (toCmd (stmtC s) mn H ns res pre0) st)
        -> exists vs', k vs'
          /\ interp specs (precond vs' pre post true (fun x => x) ns res st)
          /\ (forall x e, vs' x = Some e
            -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
              -> Logic.exprD e fE1 = Logic.exprD e fE2).
  Admitted.
  (*Proof.
    induction s; (repeat post; intuition;
      repeat (pre_implies || use_In || case_option); try use_error_message; try Stmt_use_IH;
        try (pre_evalu; exprC_correct); evalu;
          my_descend; eauto; propxFo;
            my_descend; repeat (my_descend; cancl || (step auto_ext; my_descend))).
  Qed.*)

  Definition normalWf' := normalWf.

  Definition scopey post := List.Forall (wellScoped (NQuants post ++ "result" :: fvs)).
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

  Lemma Stmt_vc : forall pre post im mn (H : importsGlobal im) ns res xs,
    normalWf' fvs pre
    -> normalWf' ("result" :: fvs) post
    -> ~In "rp" ns
    -> (forall x, In x xs -> In x ns)
    -> ~In "result" fvs
    -> ~In "result" (NQuants pre)
    -> ~In "result" (NQuants post)
    -> scopey post (NImpure post)
    -> scopey' "result" (NImpure pre)
    -> (forall x, In x fvs -> ~In x (NQuants pre))
    -> (forall x, In x fvs -> ~In x (NQuants post))
    -> forall s pre0 k,
      (forall specs st,
        interp specs (pre0 st)
        -> exists vs, interp specs (precond vs pre post true (fun x => x) ns res st)
          /\ stmtD pre post fvs vs s k
          /\ (forall x e, vs x = Some e
            -> forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
              -> Logic.exprD e fE1 = Logic.exprD e fE2))
      -> stmtV xs s
      -> vcs (VerifCond (toCmd (stmtC s) mn H ns res pre0)).
  Admitted.
  (*Proof.
    induction s.

    Ltac t := wrap0; repeat (pre_implies || use_In || case_option); simpl in *; intuition eauto;
      try (pre_evalu; exprC_correct); try evalu;
        try match goal with
              | [ IH : _ |- _ ] => eapply IH; eauto; intros;
                match goal with
                  | [ H : interp _ _ |- _ ] => eapply Stmt_post in H;
                    Stmt_use_IH'; (cbv beta in *; eauto)
                end
            end.

    t.

    t.

    wrap0; repeat (pre_implies || use_In || case_option); simpl in *; intuition eauto;
      try (pre_evalu; exprC_correct); try evalu.

    case_eq (sentail fvs pre (nsubst "result" e0 post)); intros.
    Focus 2.
    rewrite H23 in *; inversion H11.
    rewrite H23 in *.
    descend.
    step auto_ext.
    step auto_ext.
    descend.
    cancl.
    specialize (sentail_sound fvs (fo_set x1 "result" (Dyn (Regs st Rv))) (@SNil _ _) _ _ _ H23); intuition.
    unfold SubstsH in *; simpl in *.
    eapply Himp_trans; [ | eapply nsubst_bwd; eauto ].
    eapply Himp_trans; [ | apply H22 ].

    Lemma weaken_normalD : forall n xs fE fE',
      normalWf xs n
      -> (forall x, In x xs -> fE x = fE' x)
      -> normalD n fE ===> normalD n fE'.
    Admitted.

    eapply weaken_normalD; eauto.
    intros.
    unfold fo_set.
    destruct (string_dec x5 "result"); subst; tauto.
    2: eauto.
    3: simpl; unfold not; intuition (subst; eauto).
    4: simpl; tauto.

    Focus 2.
    unfold fo_set at 1; simpl.
    etransitivity; try (symmetry; apply H13).
    apply H14.
    unfold fo_set; intros.
    destruct (string_dec y "result"); subst; eauto; exfalso; eauto.

    2: simpl; eauto.

    eapply Forall_forall; intros.
    eapply in_map_iff in H20; destruct H20; intuition subst.
    eapply Forall_forall in H25; try apply H7.

    Lemma wellScoped_psubst : forall x e p fvs,
      wellScoped (x :: fvs) p
      -> (forall fE1 fE2, (forall y, In y fvs -> fE1 y = fE2 y)
        -> Logic.exprD e fE1 = Logic.exprD e fE2)
      -> wellScoped fvs (psubst x e p).
    Admitted.

    eapply wellScoped_psubst.
    eapply wellScoped_weaken; eauto.
    simpl; intuition idtac.
    apply in_app_or in H; intuition eauto using in_or_app.
    simpl in *; intuition eauto using in_or_app.
    eauto using in_or_app.
  Qed.*)
End fvs.

Lemma scopey_normalize : forall fvs post post' bvs',
  post' = normalize post
  -> wellScoped ("result" :: fvs) post
  -> boundVars post = Some bvs'
  -> (forall x, In x bvs' -> ~In x ("result" :: fvs))
  -> predExt post
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
  -> predExt p
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
  2: eauto.
  simpl; intuition (subst; eauto using In_notInList).
Qed.

Local Hint Immediate normalize_NImpure_keeps.

(** Main statement compiler/combinator/macro *)
Definition Stmt
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
  pose (pre' := normalize pre).
  pose (post' := normalize post).
  apply (WrapC (stmtC s)
    (precond vs pre' post')
    (fun _ _ _ _ _ => [| False |])%PropX
    (* Unsatisfiable postcondition, since we won't allow running off the end of
     * a function body without returning *)

    (* VERIFICATION CONDITION *)
    (fun _ ns _ =>
      incl xs ns
      :: (~In "rp" ns)
      :: stmtV xs s
      :: stmtD pre' post' fvs vs s (fun _ => False)
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
      :: predExt pre
      :: predExt post
      :: nil)); [
        abstract (wrap0; match goal with
                           | [ H : interp _ _ |- _ ] => eapply Stmt_post in H; eauto; repeat (post; eauto 6)
                         end; post)
        | abstract (wrap0; match goal with
                             | [ H : wellScoped _ _ |- _ ] =>
                               solve [ eapply Stmt_vc; [ eapply normalize_wf; try apply H; eauto 2
                                 | eapply normalize_wf; eauto
                                 | .. ];
                               eauto 6 ]
                           end) ].
Defined.
