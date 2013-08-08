Require Import MyMalloc MyFree.
Require Import GeneralTactics VariableLemmas.
Require Import SyntaxExpr SemanticsExpr CompileExpr.
Require Import Semantics Safety CompileStatement SemanticsLemmas Syntax.
Require Import WrittingPrograms.
Set Implicit Arguments.

Section Fibonacci.
Variable functions : W -> option (Callee).

Definition FibLoop :=
  While (e_lt "i" input){{
    "tmp" <- SyntaxExpr.Var "Fn1";:
    "Fn1" <- SyntaxExpr.Binop Plus (SyntaxExpr.Var "Fn0") (SyntaxExpr.Var "Fn1");:
    "Fn0" <- SyntaxExpr.Var "tmp";:
    "i" <- add1 "i"
  }}.

Definition Fib1 n:= 
  (input <- (SyntaxExpr.Const n));:
  ("i" <- $$0);:
  ("Fn0" <- ($$0));:
  ("Fn1" <- ($$1));:
  FibLoop;:
  (output <- (## "Fn0")).

Lemma Safe_FibLoop : forall s, Safety.Safe functions FibLoop s.
  unfold FibLoop; cofix; solve_safe.
Qed.

Hint Immediate Safe_FibLoop.

Lemma Safe_Fib1: forall n s, Safety.Safe functions (Fib1 n) s.
  solve_safe.
Qed.



Fixpoint Fibonacci n:=
  match n with
    | O => 0
    | S n' =>
      match n' with
        | O => 1
        | S n'' => (Fibonacci n'') + (Fibonacci n')
      end
  end.

Lemma FibProperty: forall n, Fibonacci (n + 2 ) = Fibonacci (n) + Fibonacci (n+1). 
  induction n; simpl; intuition.
  assert (n + 2 = S (S n)) by omega.
  assert (n + 1 = (S n)) by omega.
  rewriter; simpl; auto.
Qed.  

Definition FibInvariant n (s : st) :=
  fst s "Fn0" = natToW (Fibonacci (wordToNat (fst s "i")))
  /\ fst s "Fn1" = natToW (Fibonacci (wordToNat (fst s "i") + 1))
  /\ (fst s "i" <= n)%word
  /\ fst s "input" = n.

Hint Rewrite roundTrip_1 : N.

Lemma plus_1 : forall n, n + 1 = S n.
  intros; omega.
Qed.

Hint Rewrite plus_1 natToW_plus : N.

Hint Rewrite wordToNat_wplus using (eapply goodSize_weaken; [ eassumption | nomega ]) : N.

Ltac wltb :=
  repeat match goal with
           | [ H : _ -> False |- _ ] => apply wltb_1 in H
           | [ H : _ = _ |- _ ] => apply wltb_0 in H
         end.


Lemma Correct_FibLoop : forall n st st', RunsTo functions FibLoop st st'
    -> FibInvariant n st
    -> fst st' "i" = n /\ FibInvariant n st'.
  intros; use_loop_inv (FibInvariant n).

  unfold FibInvariant in *; intuition (subst; unfold input in *; simpl in *); wltb;
  try (apply wordToNat_inj;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *; nomega
      end).
  

  unfold FibInvariant, input, upd in *; simpl in *.
  solve_correct; intuition (subst; unfold input in *; simpl in *);
    rewriter;
  repeat f_equal. eapply wltb_1 in H0. 
  erewrite next; eauto.
  erewrite <- next; eauto.
  
  assert (rew: wordToNat (vs0 "i") + 1 + 1 = wordToNat (vs0 "i") + 2) by omega;
  rewrite rew; clear rew.
  rewrite FibProperty.
  pre_nomega; f_equal.

  wltb. apply H0.
  apply H2.
  pre_nomega.
  wltb.
  rewrite <- (next _ _ (vs0 "input")) in H3; nomega.
Qed.

Hint Rewrite roundTrip_0 : N.

Theorem Correct_Fib1 : forall n st st', RunsTo functions (Fib1 n) st st'
    -> Output st' = Fibonacci (wordToNat n).
  intros.
  solve_correct_with FibLoop.
  simpl in *.

  eapply Correct_FibLoop in H5; intuition eauto;
    unfold FibInvariant, Output, getVar, upd, sel in *; intuition idtac.
  simpl in *; congruence.
  nomega.
Qed.

Print ReadAt.

Open Scope expr.

Locate ".++".



Definition FibLoop2:= While (##"i" .< ##input) {{
    ReadAt "temp1" ##"fibs" (##"i");:
    ReadAt "temp1" ##"fibs" (##"i" .+ $$1);:  
    (##"fibs" [##"i" .+ $$2] *<- (##"temp1" .+ ##"temp2"));:
    ("i".++)
  }}.



Definition Fib2 n:= 
  (input <- $$n);:
  ("fibs" <- new (##input .+ $$2);:
  (##"fibs" [$$0] *<- ($$0));:
  (##"fibs" [$$1] *<- ($$1));:
  ("i" <- $$0);:
  FibLoop2;:
  ReadAt output ##"fibs" (##input)).

Lemma safe_trans: forall arrays arr x1 x2,
  (x2 < x1 )%word->
  safe_access arrays (arr) (x1 ) -> 
  safe_access arrays (arr) (x2 ).
  unfold safe_access; intros.
  openHyp; descend.
  clear H0.
  nomega.
Qed.


  Lemma ltb_back: forall a b, 
    wneb (if wltb a b then $ (1) else $ (0)) $0 = true ->
    (a < b)%word.
    intros.
    unfold wltb in *.
    destruct ( wlt_dec a b) eqn:?; eauto.
    unfold wneb in H; destruct weq in H; eauto. discriminate.
    contradict n0; auto.
  Qed.
  

Lemma Safe_FibLoop2 : forall s,
  goodSize (wordToNat ((fst s) input) + 2) ->
  safe_access (snd s) ((fst s) [##("fibs") ]) ((fst s) [##input .+ $$2 ]) ->
  Safety.Safe functions FibLoop2 s.
  unfold FibLoop2; cofix.
  safe1.
  repeat (auto; safe1; evalRT); updSimpl;
  simpl in *.
  eapply safe_trans; eauto.
  pre_nomega; apply ltb_back in H1. admit.

  clear H9.
  eapply safe_trans; eauto.
  pre_nomega; apply ltb_back in H1. admit.

  clear H9 H3.
  eapply safe_trans; eauto.
  pre_nomega; apply ltb_back in H1. admit.
  eapply Safe_FibLoop2.
  evalRT.
Qed.

End Fibonacci.
