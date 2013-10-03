Require Import Syntax Semantics.
Require Import SemanticsExpr.

Section functions.

Variable functions : W -> option Callee.

Inductive Outcome := 
  | OutDone : st -> Outcome
  | OutCall : W -> W -> Statement -> st -> Outcome.
                   
Inductive RunsToF : Statement -> st -> Outcome -> Prop :=
  | Skip : forall v, RunsToF Syntax.Skip v (OutDone v)
  | Seq1 : forall v v' v'' a b,
      RunsToF a v (OutDone v') -> 
      RunsToF b v' v'' -> 
      RunsToF (Syntax.Seq a b) v v''
  | Seq2 : forall v v' a b f x s,
      RunsToF a v (OutCall f x s v') -> 
      RunsToF (Syntax.Seq a b) v (OutCall f x (Syntax.Seq s b) v')
  | CallCall : forall vs arrs f arg,
      let v := (vs, arrs) in
      let f_v := exprDenote f vs in
      let arg_v := exprDenote arg vs in
      RunsToF (Syntax.Call f arg) v (OutCall f_v arg_v Syntax.Skip v).

End functions.

Section opt.

Variables src_fs tgt_fs : W -> option Callee.

Variable R : Statement -> Statement -> Prop.

Definition sim s t := forall v, (forall v', RunsToF s v (OutDone v') -> RunsToF t v (OutDone v')) \/ (forall f x s' v', RunsToF s v (OutCall f x s' v') -> exists t', RunsToF t v (OutCall f x t' v') /\ R s' t').

Hypothesis map_same_foreign : forall w spec, src_fs w = Some (Foreign spec) -> tgt_fs w = Some (Foreign spec).

Hypothesis map_same_internal : forall w body, src_fs w = Some (Internal body) -> exists body', tgt_fs w = Some (Internal body') /\ R body body'.

Hypothesis R_sim : forall s t, R s t -> sim s t.

Import Safety.

Theorem preserve_RunsTo : forall s v v', RunsTo src_fs s v v' -> forall t, R s t -> RunsTo tgt_fs t v v'.
  induction 1; simpl in *; intuition.
  admit.
  admit.
  admit.
  admit.
  destruct (R_sim _ _ H v).
  assert (RunsToF Syntax.Skip v (OutDone v)).
  econstructor.
  eapply H0 in H1.
  Hint Constructors RunsTo.
  Lemma RunsTo_RunsToF : forall t v r, RunsToF t v r -> forall v', r = OutDone v' -> RunsTo tgt_fs t v v'.
    induction 1; simpl in *; intuition.
    injection H.
    intros; subst; intuition.
    eauto.
  Qed.
  eauto using RunsTo_RunsToF.
  



Theorem preserve_safe : forall s t, R s t -> forall v, Safe src_fs s v -> Safe tgt_fs t v.
  intros.
  eapply (Safe_coind (fun t v => exists s, R s t /\ Safe src_fs s v)).
  admit.
  admit.
  intros.
  destruct H1.
  destruct H1.
  


  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
