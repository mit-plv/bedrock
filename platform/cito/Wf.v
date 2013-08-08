(* This file gives a syntactic condition for semantic good behavior of a function body,
 * with respect to not reading uninitialized variables. *)

Require Import Bool.
Require Import VariableLemmas SyntaxExpr SemanticsExpr Syntax Semantics.

Fixpoint expReads (unwritten : string -> Prop) (e : Expr) (x : string) : Prop :=
  match e with
    | Var y => x = y /\ unwritten x
    | Const _ => False
    | Binop _ e1 e2 => expReads unwritten e1 x \/ expReads unwritten e2 x
    | TestE _ e1 e2 => expReads unwritten e1 x \/ expReads unwritten e2 x
  end.

Import Syntax.

Fixpoint writes (s : Statement) (x : string) : Prop :=
  match s with
    | Assignment y _ => x = y
    | ReadAt y _ _ => x = y
    | WriteAt _ _ _ => False
    | Seq s1 s2 => writes s1 x \/ writes s2 x
    | Skip => False
    | Conditional _ s1 s2 => writes s1 x /\ writes s2 x
    | Loop _ _ => False
    | Malloc y _ => x = y
    | Free _ => False
    | Len y _ => x = y
    | Syntax.Call _ _ => False
  end.

Fixpoint reads (unwritten : string -> Prop) (s : Statement) (x : string) : Prop :=
  match s with
    | Assignment _ e => expReads unwritten e x
    | ReadAt _ e1 e2 => expReads unwritten e1 x \/ expReads unwritten e2 x
    | WriteAt e1 e2 e3 => expReads unwritten e1 x \/ expReads unwritten e2 x \/ expReads unwritten e3 x
    | Seq s1 s2 => reads unwritten s1 x \/ reads (fun x => unwritten x /\ ~writes s1 x) s2 x
    | Skip => False
    | Conditional e s1 s2 => expReads unwritten e x \/ reads unwritten s1 x \/ reads unwritten s2 x
    | Loop e s1 => expReads unwritten e x \/ reads unwritten s1 x
    | Malloc _ e => expReads unwritten e x
    | Free e => expReads unwritten e x
    | Len _ e => expReads unwritten e x
    | Syntax.Call e1 e2 => expReads unwritten e1 x \/ expReads unwritten e2 x
  end.

Lemma exprDenote_irrel : forall unwritten vs vs' e,
  (forall x, ~expReads unwritten e x)
  -> (forall x, sel vs' x <> sel vs x -> unwritten x)
  -> exprDenote e vs = exprDenote e vs'.
  induction e; simpl; intuition.
  change (sel vs s = sel vs' s).
  specialize (H0 s).
  destruct (weq (sel vs' s) (sel vs s)); eauto.
  exfalso; eauto.
  f_equal; eauto.
  rewrite IHe1 by eauto.
  rewrite IHe2 by eauto.
  auto.
Qed.

Local Hint Constructors RunsTo.

Ltac irr E vs vs' :=
  replace (exprDenote E vs) with (exprDenote E vs') in *
    by (eapply exprDenote_irrel; (cbv beta; eauto)).

Ltac irrel := simpl in *;
  match goal with
    | [ _ : context[exprDenote ?E ?vs'] |- context[exprDenote ?E ?vs] ] =>
      match vs with
        | vs' => fail 1
        | _ => irr E vs vs'
      end
  end.

Lemma prove_NoUninitializedRunsTo' : forall fs s st st', RunsTo fs s st st'
  -> forall unwritten vs'', (forall x, ~reads unwritten s x)
    -> (forall x, sel vs'' x <> sel (fst st) x -> unwritten x)
    -> exists vs''', RunsTo fs s (vs'', snd st) (vs''', snd st')
      /\ (forall x, sel vs''' x <> sel (fst st') x -> unwritten x /\ ~writes s x).
  induction 1; simpl; intuition;
    repeat match goal with
             | [ x := _ |- _ ] => subst x
           end; eauto.

  eexists; split.
  econstructor; repeat irrel; auto.
  intros.
  destruct (string_dec var x); subst; autorewrite with sepFormula in *; eauto.
  exfalso; apply H2.
  eapply exprDenote_irrel; (cbv beta; eauto).

  eexists; split.
  econstructor.
  repeat irrel; auto.
  intros.
  destruct (string_dec var x); subst; autorewrite with sepFormula in *; eauto.
  exfalso; apply H3.
  f_equal.
  irrel; auto.
  irrel; auto.

  eexists; split.
  irr arr vs vs''.
  irr idx vs vs''.
  irr value vs vs''.
  econstructor.
  repeat irrel; auto.
  auto.

  edestruct (IHRunsTo1 unwritten); clear IHRunsTo1; eauto; intuition idtac.
  edestruct (IHRunsTo2 (fun x => unwritten x /\ ~writes a x)); eauto; intuition idtac.
  eexists; split.
  eauto.
  firstorder.

  edestruct IHRunsTo; eauto; intuition idtac.
  eexists; split.
  econstructor; repeat irrel; eauto.
  firstorder.

  edestruct IHRunsTo; eauto; intuition idtac.
  eexists; split.
  econstructor 7; repeat irrel; eauto.
  firstorder.

  edestruct (IHRunsTo1 unwritten); clear IHRunsTo1; eauto; intuition idtac.
  edestruct (IHRunsTo2 unwritten x); eauto; intuition idtac.
  specialize (H6 _ H4); tauto.
  eexists; split.
  econstructor; repeat irrel; eauto.
  firstorder.

  eexists; split.
  econstructor 9; repeat irrel; eauto.
  firstorder.

  eexists; split.
  econstructor; repeat irrel; eauto.
  intros.
  destruct (string_dec var x); subst; autorewrite with sepFormula in *; eauto.

  eexists; split.
  irr arr vs vs''.
  econstructor; repeat irrel; eauto.
  firstorder.

  eexists; split.
  econstructor; repeat irrel; eauto.
  intros.
  destruct (string_dec var x); subst; autorewrite with sepFormula in *; eauto.
  irr arr vs'' vs; tauto.

  eexists; split.
  econstructor; repeat irrel; eauto.
  firstorder.

  eexists; split.
  econstructor 14; repeat irrel; eauto.
  firstorder.
Qed.  

Theorem prove_NoUninitializedRunsTo : forall s,
  (forall x, ~reads (fun s => s <> "__arg")%type s x)
  -> forall fs vs a vs' a', RunsTo fs s (vs, a) (vs', a')
    -> forall vs'', sel vs'' "__arg" = sel vs "__arg"
      -> exists vs''', RunsTo fs s (vs'', a) (vs''', a').
  intros.
  eapply prove_NoUninitializedRunsTo' in H0; eauto.
  2: instantiate (1 := vs''); simpl in *; congruence.
  firstorder.
Qed.

Local Hint Constructors Safety.Safe.

Lemma prove_NoUninitializedSafe' : forall s unwritten,
  (forall x, ~reads unwritten s x)
  -> forall fs vs a, Safety.Safe fs s (vs, a)
    -> forall vs', (forall x, sel vs' x <> sel vs x -> unwritten x)
      -> Safety.Safe fs s (vs', a).
  intros; apply (@Safety.Safe_coind fs (fun s st =>
    exists unwritten,
      (forall x, ~reads unwritten s x)
      /\ exists vs, Safety.Safe fs s (vs, snd st)
        /\ (forall x, sel (fst st) x <> sel vs x -> unwritten x)));
  intuition idtac;
    repeat match goal with
             | [ H : Logic.ex _ |- _ ] => destruct H; intuition idtac
           end; simpl in *;
    match goal with
      | [ H : Safety.Safe _ _ _ |- _ ] => inversion H; clear H;
        repeat match goal with
                 | [ x : _ |- _ ] => subst x
               end; simpl in *; cbv beta; intuition idtac
    end.

  repeat irrel; auto.
  repeat irrel; auto.
  eauto 10.

  eapply prove_NoUninitializedRunsTo' in H3; eauto.
  destruct H3; intuition idtac.
  repeat esplit; eauto.
  intros.
  apply (H5 _ (not_eq_sym H2)).
  eauto.

  left; repeat irrel; eauto 10.

  right; repeat irrel; eauto 10.

  left; repeat irrel; intuition idtac.
  eauto 10.
  eapply prove_NoUninitializedRunsTo' in H2; eauto.
  destruct H2; intuition idtac.
  repeat esplit; eauto.
  firstorder.
  firstorder.

  repeat irrel; eauto.

  repeat irrel; auto.

  repeat irrel; auto.

  repeat irrel; auto.

  repeat irrel; eauto.

  right; repeat irrel.
  repeat esplit.
  eauto.
  3: instantiate (2 := vs_arg).
  3: tauto.
  2: eauto.

  Lemma expReads_trivial : forall x e unwritten,
    (forall x, ~unwritten x)
    -> expReads unwritten e x
    -> False.
    induction e; simpl; intuition eauto.
  Qed.

  Hint Resolve expReads_trivial.

  Lemma reads_trivial' : forall x s unwritten,
    (forall x, ~unwritten x)
    -> ~reads unwritten s x.
    induction s; simpl; intuition; eauto.
    eapply IHs2.
    2: eauto.
    simpl; intuition eauto.
  Qed.

  Lemma reads_trivial : forall x s,
    ~reads (fun _ => False) s x.
    intros; apply reads_trivial'; auto.
  Qed.

  intros.
  apply reads_trivial in H4; tauto.

  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
  eauto 6.
Qed.    

Theorem prove_NoUninitializedSafe : forall s,
  (forall x, ~reads (fun s => s <> "__arg")%type s x)
  -> forall fs vs a, Safety.Safe fs s (vs, a)
    -> forall vs', sel vs' "__arg" = sel vs "__arg"
      -> Safety.Safe fs s (vs', a).
  intros.
  eapply prove_NoUninitializedSafe' in H0; eauto.
  firstorder.
Qed.
