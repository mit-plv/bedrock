Require Import Syntax.
Require Import Semantics.
Import SemanticsExpr.
Import Safety.
Require Import GeneralTactics.
Import WDict.
Import WMake.

Set Implicit Arguments.

Inductive Outcome := 
  | Done : st -> Outcome
  | ToCall : W -> W -> Statement -> st -> Outcome.
                   
Inductive Step : Statement -> st -> Outcome -> Prop :=
  | Skip : forall v, Step Syntax.Skip v (Done v)
  | Seq1 : forall v v' v'' a b,
      Step a v (Done v') -> 
      Step b v' v'' -> 
      Step (Syntax.Seq a b) v v''
  | Seq2 : forall v v' a b f x s,
      Step a v (ToCall f x s v') -> 
      Step (Syntax.Seq a b) v (ToCall f x (Syntax.Seq s b) v')
  | Calling : forall vs arrs f arg,
      let v := (vs, arrs) in
      let f_v := exprDenote f vs in
      let arg_v := exprDenote arg vs in
      Step (Syntax.Call f arg) v (ToCall f_v arg_v Syntax.Skip v)
  | IfTrue : forall v v' cond t f, 
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Step t v v' -> 
      Step (Conditional cond t f) v v'
  | IfFalse : forall v v' cond t f, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      Step f v v' -> 
      Step (Conditional cond t f) v v'
  | WhileFalse : forall v cond body, 
      wneb (exprDenote cond (fst v)) $0 = false -> 
      Step (Loop cond body) v (Done v)
  | WhileTrue1 : forall v v' v'' cond body, 
      let loop := Loop cond body in
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Step body v (Done v') -> 
      Step loop v' v'' -> 
      Step loop v v''
  | WhileTrue2 : forall cond body v f x s' v', 
      let loop := Loop cond body in
      wneb (exprDenote cond (fst v)) $0 = true -> 
      Step body v (ToCall f x s' v') -> 
      Step loop v (ToCall f x (Syntax.Seq s' loop) v')
  | Assign : forall var value vs arrs, 
      let v := (vs, arrs) in
      let value_v := exprDenote value vs in
      Step (Syntax.Assignment var value) v (Done (Locals.upd vs var value_v, arrs))
  | Read : forall var arr idx vs (arrs : arrays),
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v -> 
      let value_v := Array.sel (snd arrs arr_v) idx_v in  
      Step (Syntax.ReadAt var arr idx) v (Done (Locals.upd vs var value_v, arrs))
  | Write : forall arr idx value vs (arrs : arrays), 
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v ->
      let value_v := exprDenote value vs in
      let new_arr := Array.upd (snd arrs arr_v) idx_v value_v in
      Step (Syntax.WriteAt arr idx value) v (Done (vs, (fst arrs, upd (snd arrs) arr_v new_arr)))  | Len : forall var arr vs arrs,
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      let len := natToW (length (snd arrs arr_v)) in
      Step (Syntax.Len var arr) v (Done (Locals.upd vs var len, arrs))
  | Free : forall arr vs (arrs : arrays),
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      Step (Syntax.Free arr) v (Done (vs, (fst arrs %- arr_v, snd arrs)))
  | Malloc : forall var size vs arrs addr ls,
      let v := (vs, arrs) in
      ~ (addr %in fst arrs) ->
      let size_v := wordToNat (exprDenote size vs) in
      goodSize (size_v + 2) ->
      length ls = size_v ->
      Step (Syntax.Malloc var size) v (Done (Locals.upd vs var addr, (fst arrs %+ addr, upd (snd arrs) addr ls)))
.

Definition is_backward_simulation (R : Statement -> Statement -> Prop) : Prop :=
  forall s t, 
    R s t -> 
    (forall v v',
       Step t v (Done v') -> Step s v (Done v')) /\
    (forall v f x v' t', 
       Step t v (ToCall f x t' v') -> 
       exists s', 
         Step s v (ToCall f x s' v') /\ 
         R s' t').

(* an extended one supposed to be used later *)
Definition is_backward_simulation_ext (R : Statement -> Statement -> Prop) (Rstate : vals -> vals -> Prop) : Prop :=
  forall vs s vt t, 
    R s t -> 
    Rstate vs vt ->
    (forall heap vt',
       Step t (vt, heap) (Done vt') -> 
       exists vs',
         Step s (vs, heap) (Done vs') /\
         Rstate (fst vs') (fst vt')) /\
    (forall heap f x vt' t', 
       Step t (vt, heap) (ToCall f x t' vt') -> 
       exists s' vs', 
         Step s (vs, heap) (ToCall f x s' vs') /\ 
         R s' t' /\
         Rstate (fst vs') (fst vt')).

Definition is_backward_similar s t := exists R, is_backward_simulation R /\ R s t.

(* each function can be optimized by different optimizors *)
Inductive is_backward_similar_callee : Callee -> Callee -> Prop :=
  | BothForeign : 
      forall spec1 spec2 : callTransition -> Prop, 
        (forall x, spec2 x -> spec1 x) -> 
        is_backward_similar_callee (Foreign spec1) (Foreign spec2)
  | BothInternal : 
      forall body1 body2, 
        is_backward_similar body1 body2 -> 
        is_backward_similar_callee (Internal body1) (Internal body2).

Definition is_backward_similar_fs fs1 fs2 := 
  forall (w : W) callee2,
    fs2 w = Some callee2 ->
    exists callee1,
      fs1 w = Some callee1 /\
      is_backward_similar_callee callee1 callee2.

Section Functions.

  Variable fs : W -> option Callee.

  Inductive StepsTo : Statement -> st -> st -> Prop :=
  | NoCall :
      forall s v v',
        Step s v (Done v') ->
        StepsTo s v v'
  | HasForeign :
      forall s v f x s' v' spec arrs v''',
        Step s v (ToCall f x s' v') ->
        fs f = Some (Foreign spec) -> 
        spec {| Arg := x; InitialHeap := snd v'; FinalHeap := arrs |} ->
        StepsTo s' (fst v', arrs) v''' ->
        StepsTo s v v'''
  | HasInternal :
      forall s v f x s' v' body vs_arg v'' v''',
        Step s v (ToCall f x s' v') ->
        fs f = Some (Internal body) -> 
        Locals.sel vs_arg "__arg" = x ->
        StepsTo body (vs_arg, snd v') v'' ->
        StepsTo s' (fst v', snd v'') v''' ->
        StepsTo s v v'''.

End Functions.

Hint Constructors StepsTo Step.

Lemma StepsTo_Seq : forall fs a v v', StepsTo fs a v v' -> forall b v'', StepsTo fs b v' v'' -> StepsTo fs (Syntax.Seq a b) v v''.
  induction 1; simpl; intuition eauto; inversion H0; subst; eauto.
Qed.
Hint Resolve StepsTo_Seq.

Lemma RunsTo_StepsTo : forall fs s v v', RunsTo fs s v v' -> StepsTo fs s v v'.
  induction 1; simpl; try solve [intuition eauto].

  unfold v, value_v in *; eauto.

  unfold v, arr_v, idx_v, value_v in *; econstructor; econstructor; eauto.

  unfold v, arr_v, idx_v, value_v, new_arr in *; econstructor; econstructor; eauto.
  
  inversion IHRunsTo; subst; eauto.

  inversion IHRunsTo; subst; eauto.

  unfold statement in *.
  inversion IHRunsTo1; subst; eauto.
  inversion IHRunsTo2; subst; eauto.
  
  unfold v, size_v in *; econstructor; econstructor; eauto.

  unfold v, arr_v in *; econstructor; econstructor; eauto.

  unfold v, arr_v, len in *; econstructor; econstructor; eauto.

  unfold v, arg_v in *; econstructor 2; eauto; simpl in *; eauto.

  unfold v, arg_v in *; econstructor 3; eauto; simpl in *; eauto.
Qed.

Hint Constructors RunsTo.

Lemma Done_RunsTo : forall fs s v out, Step s v out -> forall v', out = Done v' -> RunsTo fs s v v'.
  induction 1; simpl; intros; try discriminate; subst; try solve [intuition eauto]; intros.
  injection H; intros; subst; eauto.
  injection H0; intros; subst; eauto.
  econstructor; eauto.
  injection H; intros; subst; econstructor; eauto.
  injection H0; intros; subst; econstructor; eauto.
  injection H0; intros; subst; econstructor; eauto.
  injection H0; intros; subst; econstructor; eauto.
  injection H0; intros; subst; econstructor; eauto.
  injection H2; intros; subst; econstructor; eauto.
Qed.
Hint Resolve Done_RunsTo.

Lemma ToCall_Foreign_RunsTo : forall s v out, Step s v out -> forall f x s' v', out = ToCall f x s' v' -> forall fs spec, fs f = Some (Foreign spec) -> forall arrs, spec {| Arg := x; InitialHeap := snd v'; FinalHeap := arrs |} -> forall v''', RunsTo fs s' (fst v', arrs) v''' -> RunsTo fs s v v'''.
  induction 1; simpl; intros; try discriminate; subst; try solve [intuition eauto]; intros.
  injection H0; intros; subst; inversion H3; subst; econstructor; eauto.
  injection H; intros; subst; inversion H2; subst; econstructor; eauto.
  econstructor; eauto.
  injection H1; intros; subst; inversion H4; subst; econstructor; eauto.
Qed.
Hint Resolve ToCall_Foreign_RunsTo.

Lemma ToCall_Internal_RunsTo : forall s v out, Step s v out -> forall f x s' v', out = ToCall f x s' v' -> forall fs body, fs f = Some (Internal body) -> forall vs_arg v'', sel vs_arg "__arg" = x -> RunsTo fs body (vs_arg, snd v') v'' -> forall v''', RunsTo fs s' (fst v', snd v'') v''' -> RunsTo fs s v v'''.
  induction 1; simpl; intros; try discriminate; subst; try solve [intuition eauto]; intros.
  injection H0; intros; subst; inversion H4; subst; econstructor; eauto.
  destruct v''; injection H; intros; subst; inversion H3; subst; econstructor 14; eauto.
  econstructor; eauto.
  injection H1; intros; subst; inversion H5; subst; econstructor; eauto.
Qed.
Hint Resolve ToCall_Internal_RunsTo.

Lemma StepsTo_RunsTo : forall fs s v v', StepsTo fs s v v' -> RunsTo fs s v v'.
  induction 1; simpl; intuition eauto.
Qed.

Hint Resolve RunsTo_StepsTo StepsTo_RunsTo.

Hint Unfold is_backward_similar is_backward_simulation.

Lemma correct_StepsTo : forall tfs t v v', StepsTo tfs t v v' -> forall s, is_backward_similar s t -> forall sfs, is_backward_similar_fs sfs tfs -> StepsTo sfs s v v'.
  induction 1; simpl; intuition.

  destruct H0; openhyp.
  eapply H0 in H2; openhyp.
  econstructor; eauto.

  destruct H3; openhyp.
  eapply H3 in H5; openhyp.
  eapply H6 in H; openhyp.
  eapply H4 in H0; openhyp.
  inversion H8; subst.
  econstructor 2; eauto.
  eapply H11; eauto.

  destruct H4; openhyp.
  eapply H4 in H6; openhyp.
  eapply H7 in H; openhyp.
  eapply H5 in H0; openhyp.
  inversion H9; subst.
  econstructor 3; eauto.
Qed.
Hint Resolve correct_StepsTo.

Theorem correct_RunsTo : forall sfs s tfs t, is_backward_similar s t -> is_backward_similar_fs sfs tfs -> forall v v', RunsTo tfs t v v' -> RunsTo sfs s v v'.
  intuition eauto.
Qed.

Module Safety.

CoInductive StepSafe : Statement -> st -> Prop :=
  | Skip : 
      forall v, StepSafe Syntax.Skip v
  | Seq : 
      forall a b v, 
        StepSafe a v ->
        (forall v', Step a v (Done v') -> StepSafe b v') -> 
        StepSafe (Syntax.Seq a b) v
  | CallForeign : 
      forall v f arg,
        StepSafe (Syntax.Call f arg) v
  | CallInternal : 
      forall v f arg,
        StepSafe (Syntax.Call f arg) v
  | IfTrue : 
      forall v cond t f, 
        wneb (exprDenote cond (fst v)) $0 = true -> 
        StepSafe t v -> 
        StepSafe (Conditional cond t f) v
  | IfFalse : 
      forall v cond t f, 
        wneb (exprDenote cond (fst v)) $0 = false -> 
        StepSafe f v -> 
        StepSafe (Conditional cond t f) v
  | WhileFalse : 
      forall v cond body, 
        wneb (exprDenote cond (fst v)) $0 = false -> 
        StepSafe (Loop cond body) v
  | WhileTrue : 
      forall v cond body, 
        let loop := Loop cond body in
        wneb (exprDenote cond (fst v)) $0 = true -> 
        StepSafe body v ->
        (forall v', Step body v (Done v') -> StepSafe loop v') -> 
        StepSafe loop v
  | Assign : forall var value v,
      StepSafe (Syntax.Assignment var value) v
  | Read : forall var arr idx vs (arrs : arrays),
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v -> 
      StepSafe (Syntax.ReadAt var arr idx) v
  | Write : forall arr idx value vs (arrs : arrays), 
      let v := (vs, arrs) in
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v ->
      StepSafe (Syntax.WriteAt arr idx value) v
  | Len : forall var arr vs (arrs : arrays),
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      StepSafe (Syntax.Len var arr) (vs, arrs)
  | Malloc : forall var size vs (arrs : arrays),
      let size_v := exprDenote size vs in
      goodSize (wordToNat size_v + 2) ->
      StepSafe (Syntax.Malloc var size) (vs, arrs)
  | Free : forall arr vs (arrs : arrays),
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs ->
      StepSafe (Syntax.Free arr) (vs, arrs).

Definition ForeignSafe (spec : callTransition -> Prop) x a := exists a', spec {| Arg := x; InitialHeap := a; FinalHeap := a' |}.

Section Functions.

  Variable fs : W -> option Callee.

  CoInductive StepsSafe : Statement -> st -> Prop :=
    | FromStep :
        forall s v,
          StepSafe s v ->
          (forall f x s' v',
             Step s v (ToCall f x s' v') ->
             (exists spec,
                fs f = Some (Foreign spec) /\
                ForeignSafe spec x (snd v') /\
                forall a',
                  spec {| Arg := x; InitialHeap := snd v'; FinalHeap := a' |} ->
                  StepsSafe s' (fst v', a')) \/
             (exists body,
                fs f = Some (Internal body) /\
                forall vs_arg,
                  Locals.sel vs_arg "__arg" = x ->
                  StepsSafe body (vs_arg, snd v') /\
                  forall v'',
                    StepsTo fs body (vs_arg, snd v') v'' ->
                    StepsSafe s' (fst v', snd v'')))
            -> StepsSafe s v.

End Functions.

Section StepsSafe_coind.

  Variable R : (W -> option Callee) -> Statement -> st -> Prop.

  Hypothesis FromStep_case : 
    forall fs s v,
      R fs s v ->
      StepSafe s v /\
      (forall f x s' v',
         Step s v (ToCall f x s' v') ->
         (exists spec,
            fs f = Some (Foreign spec) /\
            ForeignSafe spec x (snd v') /\
            forall a',
              spec {| Arg := x; InitialHeap := snd v'; FinalHeap := a' |} ->
              R fs s' (fst v', a')) \/
         (exists body,
            fs f = Some (Internal body) /\
            forall vs_arg,
              Locals.sel vs_arg "__arg" = x ->
              R fs body (vs_arg, snd v') /\
              forall v'',
                StepsTo fs body (vs_arg, snd v') v'' ->
                R fs s' (fst v', snd v''))).

  Hint Constructors StepsSafe.

  Theorem StepsSafe_coind : forall fs s v, R fs s v -> StepsSafe fs s v.
    cofix.
    intros.
    eapply FromStep_case in H; openhyp.
    econstructor.
    eauto.
    intros.
    eapply H0 in H1; openhyp.
    left.
    eexists; intuition eauto.
    Guarded.
    right.
    eexists; intuition eauto.
    eapply H2 in H3; openhyp.
    eauto.
    eapply H2 in H3; openhyp.
    eauto.
  Qed.

End StepsSafe_coind.

Lemma Safe_StepsSafe : forall fs s v, Safe fs s v -> StepsSafe fs s v.
  admit.
Qed.

Lemma StepsSafe_Safe : forall fs s v, StepsSafe fs s v -> Safe fs s v.
  intros.
  eapply (Safe_coind (fun s v => StepsSafe fs s v)); simpl in *; intuition.

  inversion H0; subst.
  inversion H1.
  eauto.

  inversion H0; subst.
  inversion H1.
  eauto.

  Lemma StepSafe_Seq_Skip : forall s v, StepSafe s v -> StepSafe (Syntax.Seq s Syntax.Skip) v.
    admit.
  Qed.
  Hint Resolve StepSafe_Seq_Skip.

  Lemma StepsSafe_Seq_Skip : forall fs s v, StepsSafe fs s v -> StepsSafe fs (Syntax.Seq s Syntax.Skip) v.
    intros.
    eapply (StepsSafe_coind (fun fs s' v => exists s, s' = Syntax.Seq s Syntax.Skip /\ StepsSafe fs s v)); simpl; intuition eauto.
    openhyp.
    inversion H1; subst.
    eauto.
    openhyp.
    subst.
    inversion H1; subst.
    inversion H7; subst.
    inversion H2; subst.
    eapply H3 in H5; openhyp.
    left.
    eexists; intuition eauto.
    right.
    eexists; intuition eauto.
    (*here*)


    admit.
    admit.
  Qed.
  Hint Resolve StepsSafe_Seq_Skip.

  Lemma StepsSafe_Seq : forall fs a b v, StepsSafe fs (Syntax.Seq a b) v -> StepsSafe fs a v.
    intros.
    eapply (StepsSafe_coind (fun fs a v => exists b, StepsSafe fs (Syntax.Seq a b) v)); simpl; intuition.
    openhyp.
    inversion H0; subst.
    inversion H1; subst.
    eauto.

    openhyp.
    inversion H0; subst.
    edestruct H3.
    econstructor 3; eauto.
 
    left; openhyp; eexists; intuition eauto.
    right; openhyp.
    eexists; intuition eauto.
    eapply H5 in H6; openhyp.
    eexists; eauto.
    eapply H5 in H6; openhyp.
    eexists; eauto.

    eexists; eauto.
  Qed.
  Hint Resolve StepsSafe_Seq.

  eauto.

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Qed.

Hint Resolve Safe_StepsSafe StepsSafe_Safe.

Definition is_safety_preserving (R : Statement -> Statement -> Prop) : Prop :=
  forall s t,
    R s t ->
    (forall v,
      StepSafe s v ->
      StepSafe t v) /\
    (forall v f x t' v',
       Step t v (ToCall f x t' v') ->
       exists s',
         Step s v (ToCall f x s' v') /\
         R s' t').

Definition preserves_safety s t := exists R, is_safety_preserving R /\ R s t.

Inductive callee_preserves_safety : Callee -> Callee -> Prop :=
  | BothForeign : 
      forall spec1 spec2 : callTransition -> Prop, 
        (forall x a, ForeignSafe spec1 x a -> ForeignSafe spec2 x a) -> 
        callee_preserves_safety (Foreign spec1) (Foreign spec2)
  | BothInternal : 
      forall body1 body2, 
        preserves_safety body1 body2 -> 
        callee_preserves_safety (Internal body1) (Internal body2).

Definition fs_preserves_safety fs1 fs2 := 
  forall (w : W) callee1,
    fs1 w = Some callee1 ->
    exists callee2,
      fs2 w = Some callee2 /\
      callee_preserves_safety callee1 callee2.

Hint Unfold preserves_safety fs_preserves_safety.

Theorem is_backward_similar_trans : forall a b c, is_backward_similar a b -> is_backward_similar b c -> is_backward_similar a c.
  intros.
  destruct H; openhyp.
  destruct H0; openhyp.
  exists (fun a c => exists b, x a b /\ x0 b c); intuition eauto.
  unfold is_backward_simulation in *.
  intros.
  openhyp.
  split.
  intros.
  eapply H0 in H4; openhyp.
  eapply H in H3; openhyp.
  eauto.

  intros.
  eapply H0 in H4; openhyp.
  eapply H6 in H5; openhyp.
  eapply H in H3; openhyp.
  eapply H8 in H5; openhyp.
  intuition eauto.
Qed.

Theorem preserves_safety_trans : forall a b c, preserves_safety a b -> preserves_safety b c -> preserves_safety a c.
  intros.
  destruct H; openhyp.
  destruct H0; openhyp.
  exists (fun a c => exists b, x a b /\ x0 b c); intuition eauto.
  unfold is_safety_preserving in *.
  intros.
  openhyp.
  split.
  intros.
  eapply H0 in H4; openhyp.
  eapply H in H3; openhyp.
  eauto.

  intros.
  eapply H0 in H4; openhyp.
  eapply H6 in H5; openhyp.
  eapply H in H3; openhyp.
  eapply H8 in H5; openhyp.
  intuition eauto.
Qed.

Lemma correct_StepsSafe : 
  forall sfs s v, 
    StepsSafe sfs s v -> 
    forall t, 
      preserves_safety s t -> 
      forall tfs, 
        fs_preserves_safety sfs tfs -> 
        is_backward_similar_fs sfs tfs -> 
        StepsSafe tfs t v.
  intros.
  eapply (
      StepsSafe_coind (
          fun tfs t v => 
            exists sfs s, 
              StepsSafe sfs s v /\ 
              preserves_safety s t /\
              fs_preserves_safety sfs tfs /\
              is_backward_similar_fs sfs tfs
    )).
  2 : do 3 eexists; intuition eauto.
  intros.
  openhyp.

  split.
  inversion H3; subst.
  destruct H4; openhyp.
  eapply H4 in H9; openhyp.
  eauto.

  intros.
  inversion H3; subst.
  destruct H4; openhyp.
  eapply H4 in H10; openhyp.
  eapply H11 in H7; openhyp.
  eapply H9 in H7; openhyp.

  left.
  generalize H7; intro.
  eapply H5 in H7; openhyp.
  inversion H16; subst.
  eexists; intuition eauto.
  eapply H6 in H7; openhyp.
  inversion H19; subst.
  rewrite H15 in H7; injection H7; intros; subst.
  do 2 eexists; intuition eauto.

  right.
  generalize H7; intro.
  eapply H5 in H7; openhyp.
  inversion H15; subst.
  eexists; intuition eauto.

  eapply H6 in H7; openhyp.
  inversion H18; subst.
  rewrite H14 in H7; injection H7; intros; subst.
  edestruct H13; eauto.
  do 2 eexists; intuition eauto.

  eapply H6 in H7; openhyp.
  inversion H19; subst.
  rewrite H14 in H7; injection H7; intros; subst.
  edestruct H13; eauto.
  do 2 eexists; intuition eauto.

Qed.

Hint Resolve correct_StepsSafe.

Theorem correct_Safe : forall sfs s v, Safe sfs s v -> forall t, preserves_safety s t -> forall tfs, fs_preserves_safety sfs tfs -> is_backward_similar_fs sfs tfs -> Safe tfs t v.
  eauto.
Qed.

Hint Resolve correct_RunsTo correct_Safe.

Theorem correct : 
  forall sfs s tfs t, 
    is_backward_similar s t -> 
    preserves_safety s t ->
    is_backward_similar_fs sfs tfs -> 
    fs_preserves_safety sfs tfs ->
    forall v, 
      (Safe sfs s v -> Safe tfs t v) /\ 
      forall v', 
        RunsTo tfs t v v' -> RunsTo sfs s v v'.
  intuition eauto.
Qed.