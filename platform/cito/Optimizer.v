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
  | ToCall : W -> W -> Statement -> st -> Outcome
  | ToMalloc : string -> W -> Statement -> st -> Outcome.
                   
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
  | Malloc : forall var size vs arrs,
      let v := (vs, arrs) in
      let size_v := exprDenote size vs in
      Step (Syntax.Malloc var size) v (ToMalloc var size_v Syntax.Skip v)
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
.

Definition is_bisimulation (R : Statement -> Statement -> Prop) : Prop :=
  forall s t, 
    R s t -> 
    (forall v v',
       Step s v (Done v') -> Step t v (Done v')) /\
    (forall v v',
       Step t v (Done v') -> Step s v (Done v')) /\
    (forall v f x v' s', 
       Step s v (ToCall f x s' v') -> 
       exists t', 
         Step t v (ToCall f x t' v') /\ 
         R s' t') /\
    (forall v f x v' t', 
       Step t v (ToCall f x t' v') -> 
       exists s', 
         Step s v (ToCall f x s' v') /\ 
         R s' t') /\
    (forall v r x v' s',
       Step s v (ToMalloc r x s' v') ->
       exists t',
         Step t v (ToMalloc r x t' v') /\
         R s' t') /\
    (forall v r x v' t',
       Step t v (ToMalloc r x t' v') ->
       exists s',
         Step s v (ToMalloc r x s' v') /\
         R s' t').

Definition bisimilar s t := exists R, is_bisimulation R /\ R s t.

(* each function can be optimized by different optimizors, using different bisimulations *)
Inductive bisimilar_callee : Callee -> Callee -> Prop :=
  | BothForeign : forall a b, (forall x, a x <-> b x) -> bisimilar_callee (Foreign a) (Foreign b)
  | BothInternal : forall a b, bisimilar a b -> bisimilar_callee (Internal a) (Internal b).

Definition bisimilar_fs a b := 
  forall (w : W), 
    (a w = None /\ b w = None) \/
    exists x y,
      a w = Some x /\ b w = Some y /\
      bisimilar_callee x y.

Section Functions.

  Variable fs : W -> option Callee.

  Inductive StepsTo : Statement -> st -> st -> Prop :=
  | NoCall :
      forall s v v',
        Step s v (Done v') ->
        StepsTo s v v'
  | HasForeign :
      forall s v f x s' v' spec v'' v''',
        Step s v (ToCall f x s' v') ->
        fs f = Some (Foreign spec) -> 
        spec {| Arg := x; InitialHeap := snd v'; FinalHeap := snd v'' |} ->
        StepsTo s' v'' v''' ->
        StepsTo s v v'''
  | HasInternal :
      forall s v f x s' v' body vs_arg v'' v''',
        Step s v (ToCall f x s' v') ->
        fs f = Some (Internal body) -> 
        Locals.sel vs_arg "__arg" = x ->
        StepsTo body (vs_arg, snd v') v'' ->
        StepsTo s' v'' v''' ->
        StepsTo s v v'''
  | HasMalloc : 
      forall s v var x s' v' addr ls v''',
        Step s v (ToMalloc var x s' v') ->
        let vs := fst v' in
        let arrs := snd v' in
        ~ (addr %in fst arrs) ->
        let size_v := wordToNat x in
        goodSize (size_v + 2) ->
        length ls = size_v ->
        let v'' := (Locals.upd vs var addr, (fst arrs %+ addr, upd (snd arrs) addr ls)) in
        StepsTo s' v'' v''' ->
        StepsTo s v v'''.

End Functions.

Theorem RunsTo_StepsTo_equiv : forall fs s v v', RunsTo fs s v v' <-> StepsTo fs s v v'.
  admit.
Qed.

Hint Unfold bisimilar is_bisimulation.

Hint Constructors Step.

Lemma correct_StepsTo : forall sfs s v v', StepsTo sfs s v v' -> forall tfs t, bisimilar s t -> bisimilar_fs sfs tfs -> StepsTo tfs t v v'.
  induction 1; simpl; intuition.

  destruct H0.
  openhyp.
  eapply H0 in H2.
  openhyp.
  econstructor; eauto.

  destruct H3.
  openhyp.
  eapply H3 in H5.
  openhyp.
  eapply H7 in H.
  openhyp.
  generalize H4; intro; specialize (H4 f); openhyp.
  rewrite H0 in *; discriminate.
  rewrite H0 in *; injection H4; intros; subst.
  inversion H14; subst.
  econstructor 2; eauto.
  eapply H16; eauto.

  destruct H4.
  openhyp.
  eapply H4 in H6.
  openhyp.
  eapply H8 in H.
  openhyp.
  generalize H5; intro; specialize (H5 f); openhyp.
  rewrite H0 in *; discriminate.
  rewrite H0 in *; injection H5; intros; subst.
  inversion H15; subst.
  econstructor 3; eauto.

  destruct H4.
  openhyp.
  eapply H4 in H6.
  openhyp.
  eapply H10 in H.
  openhyp.
  econstructor 4; eauto.
Qed.
Hint Resolve correct_StepsTo.

Theorem correct_RunsTo : forall sfs s tfs t, bisimilar s t -> bisimilar_fs sfs tfs -> forall v v', RunsTo sfs s v v' -> RunsTo tfs t v v'.
  intros.
  eapply RunsTo_StepsTo_equiv in H1.
  eapply RunsTo_StepsTo_equiv.
  eauto.
Qed.

Theorem correct_Safe : forall sfs s tfs t, bisimilar s t -> bisimilar_fs sfs tfs -> forall v, Safe sfs s v -> Safe tfs t v.
  admit.
Qed.

Hint Resolve correct_RunsTo correct_Safe.

Lemma bisimilar_symm : forall a b, bisimilar a b -> bisimilar b a.
  exists (fun a b => bisimilar b a).
  intuition.
  unfold is_bisimulation.
  intros.
  destruct H0.
  openhyp.
  eapply H0 in H1.
  openhyp.
  intuition.

  eapply H4 in H7.
  openhyp.
  eexists; intuition eauto.

  eapply H3 in H7.
  openhyp.
  eexists; intuition eauto.

  eapply H6 in H7.
  openhyp.
  eexists; intuition eauto.

  eapply H5 in H7.
  openhyp.
  eexists; intuition eauto.
Qed.

Hint Resolve bisimilar_symm.

Hint Constructors bisimilar_callee.

Lemma bisimilar_callee_symm : forall a b, bisimilar_callee a b -> bisimilar_callee b a.
  induction 1; simpl; intuition; econstructor; firstorder.
Qed.

Hint Resolve bisimilar_callee_symm.

Lemma bisimilar_fs_symm : forall a b, bisimilar_fs a b -> bisimilar_fs b a.
  unfold bisimilar_fs; intros; specialize (H w); openhyp.
  left; eauto.
  right; eexists; eauto.
Qed.

Hint Resolve bisimilar_fs_symm.

Theorem correct : forall sfs s tfs t, bisimilar s t -> bisimilar_fs sfs tfs -> forall v, (Safe sfs s v <-> Safe tfs t v) /\ forall v', RunsTo sfs s v v' <-> RunsTo tfs t v v'.
  intuition eauto.
Qed.
