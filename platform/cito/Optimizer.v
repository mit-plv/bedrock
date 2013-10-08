Require Import Syntax.
Require Import Semantics.
Import SemanticsExpr.
Import Safety.

Inductive Outcome := 
  | Done : st -> Outcome
  | ToCall : W -> W -> Statement -> st -> Outcome.
                   
Inductive RunsToF : Statement -> st -> Outcome -> Prop :=
  | Skip : forall v, RunsToF Syntax.Skip v (Done v)
  | Seq1 : forall v v' v'' a b,
      RunsToF a v (Done v') -> 
      RunsToF b v' v'' -> 
      RunsToF (Syntax.Seq a b) v v''
  | Seq2 : forall v v' a b f x s,
      RunsToF a v (ToCall f x s v') -> 
      RunsToF (Syntax.Seq a b) v (ToCall f x (Syntax.Seq s b) v')
  | Calling : forall vs arrs f arg,
      let v := (vs, arrs) in
      let f_v := exprDenote f vs in
      let arg_v := exprDenote arg vs in
      RunsToF (Syntax.Call f arg) v (ToCall f_v arg_v Syntax.Skip v).

Definition bisimulation (R : Statement -> Statement -> Prop) := 
  forall s t, 
    R s t -> 
    forall v, 
      (exists v', 
         RunsToF s v (Done v') /\ 
         RunsToF t v (Done v')) \/ 
      (exists f x s' t' v', 
         RunsToF s v (ToCall f x s' v') /\ 
         RunsToF t v (ToCall f x t' v') /\ 
         R s' t').

Definition bisimilar s t := exists R, bisimulation R /\ R s t.

(* each function can be optimized by different optimizors, hence using different bisimulations *)
Definition bisimilar_callee (s f : option Callee) :=
  match s, f with
    | Some (Foreign a), Some (Foreign b) => forall x, a x <-> b x
    | Some (Internal a), Some (Internal b) => bisimilar a b                                      
    | None, None => True
    | _, _ => False
  end.

Definition bisimilar_fs src_fs tgt_fs := forall (w : W), bisimilar_callee (src_fs w) (tgt_fs w).

Theorem correct_RunsTo : forall sfs s tfs t, bisimilar s t -> bisimilar_fs sfs tfs -> forall v v', RunsTo sfs s v v' -> RunsTo tfs t v v'.
  intros.
  unfold bisimilar in *.
  Require Import GeneralTactics.
  openhyp.

Qed.

Theorem correct_Safe : forall sfs s tfs t, bisimilar s t -> bisimilar_fs sfs tfs -> forall v, Safe sfs s v -> Safe tfs t v.
  admit.
Qed.

Hint Resolve correct_RunsTo correct_Safe.

Lemma bisimilar_symm : forall a b, bisimilar a b -> bisimilar b a.
  admit.
Qed.

Hint Resolve bisimilar_symm.

Lemma bisimilar_fs_symm : forall a b, bisimilar_fs a b -> bisimilar_fs b a.
  admit.
Qed.

Hint Resolve bisimilar_fs_symm.

Theorem correct : forall sfs s tfs t, bisimilar s t -> bisimilar_fs sfs tfs -> forall v, (Safe sfs s v <-> Safe tfs t v) /\ forall v', RunsTo sfs s v v' <-> RunsTo tfs t v v'.
  intuition eauto.
Qed.









Section Functions.

Variable functions : W -> option Callee.

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

End Functions.





















Hint Constructors RunsTo.
Lemma RunsTo_RunsToF : forall t v r, RunsToF t v r -> forall v', r = Done v' -> RunsTo tgt_fs t v v'.
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
                            | 0 => r = Done v'
                            | S n' => exists f x s' v'', r = Call f x s' v'' /\ RunsToI src_fs n' s'
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

