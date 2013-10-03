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

Inductive RunsToI : nat -> Statement -> st -> st -> Prop :=
  | SeqI : forall v v' v'' a b n1 n2,
      RunsToI n1 a v v' -> 
      RunsToI n2 b v' v'' -> 
      RunsToI (n1 + n2) (Syntax.Seq a b) v v''
  | SkipI : forall v, RunsToI 0 Syntax.Skip v v
  | CallForeignI : forall vs arrs f arrs' spec arg,
      let v := (vs, arrs) in
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Foreign spec)
      -> spec {| Arg := arg_v; InitialHeap := arrs; FinalHeap := arrs' |}
      -> RunsToI 1 (Syntax.Call f arg) v (vs, arrs')
  | CallInternalI : forall vs arrs f arrs' body arg vs_arg vs' n,
      let v := (vs, arrs) in
      let arg_v := exprDenote arg vs in
      functions (exprDenote f vs) = Some (Internal body)
      -> Locals.sel vs_arg "__arg" = arg_v
      -> RunsToI n body (vs_arg, arrs) (vs', arrs')
      -> RunsToI (1 + n) (Syntax.Call f arg) v (vs, arrs').

End functions.

Section opt.

Variables src_fs tgt_fs : W -> option Callee.

Variable R : Statement -> Statement -> Prop.

Inductive bisim : st -> Statement -> Statement -> Prop := 
  | ToDone : forall v v' s t, RunsToF s v (OutDone v') -> RunsToF t v (OutDone v') -> bisim v s t
  | ToCall : forall v s t f x s' v' t', RunsToF s v (OutCall f x s' v') -> RunsToF t v (OutCall f x t' v') -> R s' t' -> bisim v s t.

Hypothesis map_same_foreign : forall w spec, src_fs w = Some (Foreign spec) -> tgt_fs w = Some (Foreign spec).

Hypothesis map_same_internal : forall w body, src_fs w = Some (Internal body) -> exists body', tgt_fs w = Some (Internal body') /\ R body body'.

Definition opt s := Syntax.Seq Syntax.Skip s.

Hypothesis R_opt : forall s t, R s t -> t = opt s.

Hypothesis R_bisim : forall s t, R s t -> forall v, bisim v s t.

Import Safety.

Theorem correct : forall s t, R s t -> forall v v', RunsTo tgt_fs t v v' -> RunsTo src_fs s v v'.
  intros.
  eapply R_opt in H.
  subst.
  inversion H0; subst.
  inversion H2; subst.

Hint Constructors RunsTo.
Lemma RunsTo_RunsToF : forall t v r, RunsToF t v r -> forall v', r = OutDone v' -> RunsTo tgt_fs t v v'.
  induction 1; simpl in *; intuition.
  injection H.
  intros; subst; intuition.
  eauto.
Qed.

Theorem preserve_RunsTo : forall n s v v', RunsToI src_fs n s v v' -> forall t, R s t -> RunsTo tgt_fs t v v'.
  induction n; simpl; intuition.
  specialize (R_bisim _ _ H0 v).
  inversion_clear R_bisim.
  Lemma step0 : forall n s v v', RunsToI src_fs n s v v' -> forall r, RunsToF s v r -> 
                        match n with
                            | 0 => r = OutDone v'
                            | S n' => exists f x s' v'', r = OutCall f x s' v'' /\ RunsToI src_fs n' s'
                        end.
    induction 1; simpl; intuition.
    inversion H1; subst.
    eapply IHRunsToI1 in H4.
    destruct 
    eapply IHRunsToI2 in H7.


  induction 1; simpl in *; intuition.
  admit.
  admit.
  admit.
  (* seq *)
  specialize (R_bisim _ _ H1 v).
  inversion_clear R_bisim.
  inversion H2; subst.
  eauto using RunsTo_RunsToF.
  inversion H0; subst.



  specialize (R_bisim _ _ H v).
  inversion_clear R_bisim.
  inversion H0.
  subst.
  eauto using RunsTo_RunsToF.
  inversion H0; subst.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.



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
