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

Theorem exprC_correct : forall specs P stn st xs V vs fE e e' res,
  vars_ok fE V vs
  -> exprD vs e = Some e'
  -> exprV xs e
  -> ~In "rp" xs
  -> interp specs (![locals ("rp" :: xs) V res (Regs st Sp) * P] (stn, st))
  -> exists w,
    evalRvalue stn st (exprC e xs) = Some w
    /\ Logic.exprD e' fE = Dyn w.
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
  eauto.
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

(** Helper to copy formal parameter values from a [vals] to a [fo_env] *)
Fixpoint formals (V : vals) (xs : list pr_var) (fE : fo_env) : fo_env :=
  match xs with
    | nil => fE
    | x :: xs => fo_set (formals V xs fE) x (Dyn (sel V x))
  end.

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
            | [ H : exists x, _ /\ _ |- _ ] => destruct H as [ ? [ ] ]
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

Lemma Stmt_post : forall pre post im mn (H : importsGlobal im) ns res xs,
  ~In "rp" ns
  -> (forall x, In x xs -> In x ns)
  -> forall s pre0 k,
    (forall specs st,
      interp specs (pre0 st)
      -> exists vs, interp specs (precond vs pre post true (fun x => x) ns res st)
        /\ stmtD pre post vs s k
        /\ forall x, In x xs -> vs x <> None)
    -> stmtV xs s
    -> forall specs st, interp specs (Structured.Postcondition (toCmd (stmtC s) mn H ns res pre0) st)
      -> exists vs', k vs'
        /\ interp specs (precond vs' pre post true (fun x => x) ns res st)
        /\ forall x, In x xs -> vs' x <> None.
Proof.
  induction s; (repeat post; intuition;
    repeat (pre_implies || use_In || case_option); try use_error_message; try Stmt_use_IH;
      try (pre_evalu; exprC_correct); evalu;
        my_descend; eauto; propxFo;
          my_descend; repeat (my_descend; cancl || (step auto_ext; my_descend))).
Qed.

Lemma Stmt_vc : forall pre post im mn (H : importsGlobal im) ns res xs,
  ~In "rp" ns
  -> (forall x, In x xs -> In x ns)
  -> forall s pre0 k,
    (forall specs st,
      interp specs (pre0 st)
      -> exists vs, interp specs (precond vs pre post true (fun x => x) ns res st)
        /\ stmtD pre post vs s k
        /\ forall x, In x xs -> vs x <> None)
    -> stmtV xs s
    -> vcs (VerifCond (toCmd (stmtC s) mn H ns res pre0)).
Proof.
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
  (* Here we need some reasoning about the correctness of entailment. *)
  admit.
Qed.

(** Main statement compiler/combinator/macro *)
Definition Stmt
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
      :: (forall x, In x xs -> vs x <> None)
      :: stmtD pre' post' vs s (fun _ => False)
      :: nil)); [
        abstract (wrap0; match goal with
                           | [ H : interp _ _ |- _ ] => eapply Stmt_post in H; eauto; post
                         end)
        | abstract (wrap0; eapply Stmt_vc; eauto) ].
Defined.
