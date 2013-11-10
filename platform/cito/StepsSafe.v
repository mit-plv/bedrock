Require Import Syntax.
Require Import Semantics.
Require Import StepsTo.
Require Import GeneralTactics.
Import SemanticsExpr.
Import WDict.
Import WMake.
Import Safety.

Set Implicit Arguments.

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

Section StepSafe_coind.

  Variable R : Statement -> st -> Prop.

  Hypothesis Seq_case : 
    forall a b v, 
      R (Syntax.Seq a b) v ->
      R a v /\
      forall v', Step a v (Done v') -> R b v'.
        
  Hypothesis If_case : 
    forall v cond t f, 
      R (Conditional cond t f) v ->
      wneb (exprDenote cond (fst v)) $0 = true /\
      R t v \/
      wneb (exprDenote cond (fst v)) $0 = false /\ 
      R f v.

  Hypothesis While_case : 
    forall v cond body, 
      let loop := Loop cond body in
      R loop v ->
      wneb (exprDenote cond (fst v)) $0 = false \/
      wneb (exprDenote cond (fst v)) $0 = true /\
      R body v /\
      forall v', 
        Step body v (Done v') -> 
        R loop v'.

  Hypothesis Read_case : 
    forall var arr idx vs (arrs : arrays),
      let v := (vs, arrs) in
      R (Syntax.ReadAt var arr idx) v ->
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v.

  Hypothesis Write_case : 
    forall arr idx value vs (arrs : arrays), 
      let v := (vs, arrs) in
      R (Syntax.WriteAt arr idx value) v ->
      let arr_v := exprDenote arr vs in
      let idx_v := exprDenote idx vs in
      safe_access arrs arr_v idx_v.

  Hypothesis Len_case : 
    forall var arr vs (arrs : arrays),
      R (Syntax.Len var arr) (vs, arrs) ->
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs.

  Hypothesis Malloc_case : 
    forall var size vs (arrs : arrays),
      R (Syntax.Malloc var size) (vs, arrs) ->
      let size_v := exprDenote size vs in
      goodSize (wordToNat size_v + 2).

  Hypothesis Free_case : 
    forall arr vs (arrs : arrays),
      R (Syntax.Free arr) (vs, arrs) ->
      let arr_v := exprDenote arr vs in
      arr_v %in fst arrs.

  Hint Constructors StepSafe.

  Theorem StepSafe_coind : forall s v, R s v -> StepSafe s v.
    cofix.
    intros.
    destruct v; destruct s.

    eauto.
    Guarded.

    econstructor.
    eapply Read_case; eauto.
    Guarded.

    econstructor.
    eapply Write_case; eauto.
    Guarded.

    eapply Seq_case in H; openhyp.
    econstructor; eauto.
    Guarded.

    eauto.
    Guarded.

    eapply If_case in H; openhyp.
    econstructor; eauto.
    Guarded.
    econstructor 6; eauto.
    Guarded.

    eapply While_case in H; openhyp.
    econstructor; eauto.
    Guarded.
    econstructor 8; eauto.
    Guarded.

    econstructor.
    eapply Malloc_case; eauto.
    Guarded.

    econstructor.
    eapply Free_case; eauto.
    Guarded.

    econstructor.
    eapply Len_case; eauto.
    Guarded.

    eauto.
    Guarded.
  Qed.

End StepSafe_coind.

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

Lemma StepsSafe_Seq1 : forall fs a b v, StepsSafe fs (Syntax.Seq a b) v -> StepsSafe fs a v.
  intros.
  eapply (StepsSafe_coind (fun fs a v => StepsSafe fs a v \/ exists b, StepsSafe fs (Syntax.Seq a b) v)).
  clear.
  intros.
  openhyp.
  simpl; intuition.
  inversion H; subst.
  eauto.

  inversion H; subst.
  eapply H2 in H0; openhyp.
  left.
  eexists; intuition eauto.
  right.
  eexists; intuition eauto.
  eapply H3 in H4; openhyp.
  left; eauto.
  eapply H3 in H4; openhyp.
  left; eauto.

  simpl; intuition.
  inversion H; subst.
  inversion H0; subst.
  eauto.

  inversion H; subst.
  edestruct H2.
  econstructor 3; eauto.
  
  left; openhyp; eexists; intuition eauto.
  right; openhyp.
  eexists; intuition eauto.
  eapply H4 in H5; openhyp.
  left; eauto.
  eapply H4 in H5; openhyp.
  right; eexists; eauto.

  right; eexists; eauto.
Qed.
Hint Resolve StepsSafe_Seq1.

Lemma StepsSafe_Seq2 : forall fs a v v', StepsTo fs a v v' -> forall b, StepsSafe fs (Syntax.Seq a b) v -> StepsSafe fs b v'.
  induction 1; simpl; intuition.

  inversion H0; subst.
  inversion H1; subst.
  econstructor.
  eauto.
  intros.
  edestruct H2.
  econstructor; eauto.
  left; eauto.
  right; eauto.

  eapply IHStepsTo.
  inversion H3; subst.
  edestruct H5.
  econstructor 3; eauto.
  openhyp.
  rewrite H0 in H6; injection H6; intros; subst.
  eauto.
  openhyp.
  rewrite H0 in H6; discriminate.

  eapply IHStepsTo2.
  inversion H4; subst.
  edestruct H6.
  econstructor 3; eauto.
  openhyp.
  rewrite H0 in H1; discriminate.
  openhyp.
  rewrite H0 in H1; injection H1; intros; subst.
  edestruct H7.
  eauto.
  eauto.
Qed.
Hint Resolve StepsSafe_Seq2.

Lemma StepsSafe_Seq : 
  forall fs a b v, 
    StepsSafe fs (Syntax.Seq a b) v -> 
    StepsSafe fs a v /\
    forall v',
      StepsTo fs a v v' ->
      StepsSafe fs b v'.
  intuition eauto.
Qed.

Lemma StepsSafe_While1 :
  forall fs e b v,
    StepsSafe fs (Syntax.Loop e b) v ->
    wneb (exprDenote e (fst v)) $0 = true -> 
    StepsSafe fs b v.
Proof.
  intros.
  inversion H; subst.
  inversion H1.
  subst.
  replace (wneb _ _) with true in H6; discriminate.

  unfold loop0, loop1 in *; clear loop0 loop1.
  subst.
  econstructor; eauto.
  intros.
  edestruct H2.
  econstructor 9; eauto.
  openhyp.
  left; eexists; intuition eauto.
  openhyp.
  right; eexists; intuition.
  eauto.
  eapply H7 in H9; openhyp.
  eauto.
  eapply H7 in H9; openhyp.
  eauto.
Qed.
Hint Resolve StepsSafe_While1.

Lemma StepsSafe_While2 : 
  forall fs b v v', 
    StepsTo fs b v v' -> 
    forall e, 
      wneb (exprDenote e (fst v)) $0 = true -> 
      let loop := Syntax.Loop e b in
      StepsSafe fs loop v -> 
      StepsSafe fs loop v'.
Proof.
  induction 1; simpl; intuition.

  inversion H1; subst.
  inversion H2.
  subst.
  replace (wneb _ _) with true in H7; discriminate.

  unfold loop0, loop1 in *; clear loop0 loop1.
  subst.

  econstructor.
  eauto.
  intros.
  edestruct H3.
  econstructor; eauto.
  left; eauto.
  right; eauto.

  inversion H4; subst.
  edestruct H6.
  econstructor 9; eauto.
  openhyp.
  rewrite H0 in H7; injection H7; intros; subst.
  eapply H9 in H1.
  eapply StepsSafe_Seq in H1; openhyp.
  eauto.

  openhyp.
  rewrite H0 in H7; discriminate.

  inversion H5; subst.
  edestruct H7.
  econstructor 9; eauto.
  openhyp.
  rewrite H0 in H1; discriminate.

  openhyp.
  rewrite H0 in H1; injection H1; intros; subst.
  edestruct H8.
  eauto.
  eapply StepsSafe_Seq in H10.
  2 : eauto.
  openhyp.
  eauto.
Qed.
Hint Resolve StepsSafe_While2.

Lemma StepsSafe_While : 
  forall fs e b v,
    let loop := Syntax.Loop e b in
    StepsSafe fs loop v ->
    wneb (exprDenote e (fst v)) $0 = false \/
    wneb (exprDenote e (fst v)) $0 = true /\
    StepsSafe fs b v /\
    forall v',
      StepsTo fs b v v' ->
      StepsSafe fs loop v'.
Proof.
  intros.
  unfold loop in *; clear loop.
  destruct (Sumbool.sumbool_of_bool (wneb (exprDenote e (fst v)) $0)).
  right; intuition eauto.
  left; eauto.
Qed.

Hint Resolve RunsTo_StepsTo StepsTo_RunsTo.

Lemma StepsSafe_Safe : forall fs s v, StepsSafe fs s v -> Safe fs s v.
  intros.
  eapply (Safe_coind (fun s v => StepsSafe fs s v)).

  clear; intros.
  inversion H; subst.
  inversion H0.
  eauto.

  clear; intros.
  inversion H; subst.
  inversion H0.
  eauto.

  intros.
  split.
  eauto.
  intros.
  eauto.

  intros.
  inversion H0; subst.
  inversion H1; subst.
  left; intuition; econstructor; eauto.
  right; intuition; econstructor; eauto.

  intros.
  eapply StepsSafe_While in H0.
  openhyp.
  intuition.
  intuition eauto.

  clear; intros.
  inversion H; subst.
  inversion H0.
  eauto.

  clear; intros.
  inversion H; subst.
  inversion H0.
  eauto.

  clear; intros.
  inversion H; subst.
  inversion H0.
  eauto.

  clear; intros.
  inversion H; subst.
  edestruct H1.
  eauto.
  openhyp.
  destruct H3.
  left; do 2 eexists; intuition eauto.
  openhyp.
  right; do 2 eexists; intuition eauto.
  edestruct H3; eauto.

  eauto.
Qed.

Lemma Safe_StepSafe : forall fs s v, Safe fs s v -> StepSafe s v.
  intros.
  eapply (StepSafe_coind (fun s v => Safe fs s v)).

  clear; intros.
  inversion H; subst.
  intuition.

  clear; intros.
  inversion H; subst.
  left; intuition.
  right; intuition.

  clear; intros.
  unfold loop in *; clear loop.
  inversion H.
  unfold statement0, statement1 in *; clear statement0 statement1.
  subst.
  right; intuition.
  left; intuition.

  clear; intros.
  inversion H.
  intuition.

  clear; intros.
  inversion H.
  intuition.

  clear; intros.
  inversion H.
  intuition.

  clear; intros.
  inversion H.
  intuition.

  clear; intros.
  inversion H.
  intuition.

  eauto.
Qed.
Hint Resolve Safe_StepSafe.

Hint Constructors Safe.

Lemma Safe_Step_ToCall : 
  forall s v tocall, 
    Step s v tocall ->
    forall f x s' v',
      tocall = ToCall f x s' v' ->
      forall fs,
        Safe fs s v ->
        (exists spec,
           fs f = Some (Foreign spec) /\
           ForeignSafe spec x (snd v') /\
           forall a',
             spec {| Arg := x; InitialHeap := snd v'; FinalHeap := a' |} ->
             Safe fs s' (fst v', a')) \/
        (exists body,
           fs f = Some (Internal body) /\
           forall vs_arg,
             Locals.sel vs_arg "__arg" = x ->
             Safe fs body (vs_arg, snd v') /\
             forall v'',
               StepsTo fs body (vs_arg, snd v') v'' ->
               Safe fs s' (fst v', snd v'')).
Proof.
  induction 1; simpl; try discriminate; try solve [intuition].

  intros.
  inversion H2; subst.
  eauto.

  intros.
  injection H0; intros; subst.
  inversion H1; subst.
  edestruct IHStep; eauto.
  openhyp.
  left; eexists; intuition eauto; econstructor; eauto.
  openhyp.
  right; eexists; intuition eauto.
  eapply H3 in H5; openhyp.
  eauto.
  generalize H5; intro.
  eapply H3 in H5; openhyp.
  econstructor; eauto.

  intros.
  unfold v, f_v, arg_v in *; clear v f_v arg_v.
  symmetry in H; injection H; intros; subst.
  inversion H0; subst.
  left; eexists; intuition eauto; eexists; eauto.
  right; eexists; intuition eauto.

  intros.
  inversion H2; subst.
  eapply IHStep; eauto.
  rewrite H in H7; discriminate.

  intros.
  inversion H2; subst.
  rewrite H in H7; discriminate.
  eapply IHStep; eauto.

  intros.
  inversion H3.
  unfold statement0, statement1 in *; clear statement0 statement1.
  subst.
  eapply IHStep2; eauto.
  rewrite H in H7; discriminate.

  intros.
  unfold loop in *; clear loop.
  symmetry in H1; injection H1; intros; subst.
  inversion H2.
  unfold statement0, statement1 in *; clear statement0 statement1.
  subst.
  edestruct IHStep; eauto.
  openhyp.
  left; eexists; intuition eauto.
  openhyp.
  right; eexists; intuition eauto.
  eapply H4 in H7; openhyp.
  eauto.
  generalize H7; intro.
  eapply H4 in H7; openhyp.
  econstructor; eauto.
  rewrite H in H6; discriminate.
Qed.
Hint Resolve Safe_Step_ToCall.

Lemma Safe_StepsSafe : forall fs s v, Safe fs s v -> StepsSafe fs s v.
  intros; eapply (StepsSafe_coind (fun fs s v => Safe fs s v)); eauto.
Qed.