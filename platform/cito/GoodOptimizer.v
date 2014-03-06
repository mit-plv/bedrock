Set Implicit Arguments.

Require Import Syntax.
Require Import String.

Definition Optimizer := Stmt -> string -> Stmt.

Definition compose (f g : Optimizer) : Optimizer := fun s r => g (f s r) r.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Semantics.
  Module Import SemanticsMake := Semantics.Make E.

  Section TopSection.

    Definition PreserveRunsTo (opt : Optimizer) :=  forall ret fs s v v', RunsTo fs (opt s ret) v v' -> exists vs', RunsTo fs s v (vs', snd v') /\ Locals.sel vs' ret = Locals.sel (fst v') ret.

    Definition PreserveSafe (opt : Optimizer) := forall fs s v, Safe fs s v -> forall ret, Safe fs (opt s ret) v.

    Require Import GetLocalVars.
    Require Import Depth.
    Require Import IL.

    Definition PreserveGoodSize (opt : Optimizer) :=
      forall stmt argvars retvar, 
        let size s := List.length (get_local_vars s argvars retvar) + depth s in
        goodSize (size stmt) -> 
        goodSize (size (opt stmt retvar)).

    Require Import CompileStmtSpec.
    Require Import List.

    Definition PreserveSynReq (opt : Optimizer) :=
      forall stmt argvars retvar, 
        let vars s := argvars ++ get_local_vars s argvars retvar in
        let stmt' := opt stmt retvar in
        syn_req (vars stmt) (depth stmt) stmt ->
        syn_req (vars stmt') (depth stmt') stmt'.

    Definition GoodOptimizer opt := 
      PreserveRunsTo opt /\
      PreserveSafe opt /\ 
      PreserveGoodSize opt /\
      PreserveSynReq opt.

    Require Import GoodFunc.
    Require Import SyntaxFunc.
    Definition PreserveGoodSize' (opt : Optimizer) :=
      forall f, 
        GoodFunc f -> 
        let s := opt (Body f) (RetVar f) in
        goodSize (length (get_local_vars s (ArgVars f) (RetVar f)) + depth s).

    Definition PreserveSynReq' (opt : Optimizer) :=
      forall f, 
        GoodFunc f -> 
        let s := opt (Body f) (RetVar f) in
        syn_req (ArgVars f ++ get_local_vars s (ArgVars f) (RetVar f)) (depth s) s.

    Lemma GoodOptimizer_Safe : forall opt, GoodOptimizer opt -> PreserveSafe opt.
      unfold GoodOptimizer; intuition.
    Qed.

    Lemma GoodOptimizer_RunsTo : forall opt, GoodOptimizer opt -> PreserveRunsTo opt.
      unfold GoodOptimizer; intuition.
    Qed.

    Require Import GeneralTactics.

    Lemma GoodFunc_GoodOptimizer_goodSize : forall opt, GoodOptimizer opt -> PreserveGoodSize' opt.
      unfold GoodOptimizer.
      intros.
      openhyp.
      unfold PreserveGoodSize'.
      unfold PreserveGoodSize in *.
      intros.
      simpl in *.
      eapply H1; eauto.
      destruct H3; openhyp; eauto.
    Qed.

    Lemma GoodFunc_GoodOptimizer_syn_req : forall opt, GoodOptimizer opt -> PreserveSynReq' opt.
      unfold GoodOptimizer.
      intros.
      openhyp.
      unfold PreserveSynReq'.
      unfold PreserveSynReq in *.
      intros.
      simpl in *.
      eapply H2; eauto.
      eapply GoodFunc_syn_req; eauto.
    Qed.

    Lemma PreserveRunsTo_trans : forall a b, PreserveRunsTo a -> PreserveRunsTo b -> PreserveRunsTo (compose a b).
      unfold PreserveRunsTo, compose; intros.
      eapply H0 in H1; eauto; openhyp.
      eapply H in H1; eauto; openhyp.
      descend; intuition eauto.
    Qed.

    Lemma PreserveSafe_trans : forall a b, PreserveSafe a -> PreserveSafe b -> PreserveSafe (compose a b).
      unfold PreserveSafe, compose; intros.
      eauto.
    Qed.

    Lemma PreserveGoodSize_trans : forall a b, PreserveGoodSize a -> PreserveGoodSize b -> PreserveGoodSize (compose a b).
      unfold PreserveGoodSize, compose; intros.
      eauto.
    Qed.

    Lemma PreserveSynReq_trans : forall a b, PreserveSynReq a -> PreserveSynReq b -> PreserveSynReq (compose a b).
      unfold PreserveSynReq, compose; intros.
      eauto.
    Qed.

    Lemma GoodOptimizer_trans : 
      forall a b,
        GoodOptimizer a ->
        GoodOptimizer b ->
        GoodOptimizer (compose a b).
    Proof.
      unfold GoodOptimizer; intros.
      openhyp.
      split.
      eapply PreserveRunsTo_trans; eauto.
      split.
      eapply PreserveSafe_trans; eauto.
      split.
      eapply PreserveGoodSize_trans; eauto.
      eapply PreserveSynReq_trans; eauto.
    Qed.

  End TopSection.

End Make.