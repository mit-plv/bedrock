Require Import MyMalloc MyFree.
Require Import GeneralTactics variables.
Require Import SyntaxExpr SemanticsExpr CompileExpr.
Require Import Semantics Safety CompileStatement SemanticsLemmas Syntax.
Require Import WrittingPrograms.
Set Implicit Arguments.

Open Scope expr.

Section TrivialProg.
Variable functions : W -> option (Callee).
Variable v: st.

Definition InOut input:= "input" <- Const input;: output <- ##("input").

Lemma Safe_InOut: forall W, Safety.Safe functions (InOut W) v.
  solve_safe.
Qed.

Lemma Correct_InOut: forall w, forall st st', RunsTo functions (InOut w) st st' -> Output st' = w.
  solve_correct; tauto.
Qed.
End TrivialProg.
  
Section UseArrayProg.
Variable functions : W -> option (Callee).
Variable v: st.

Definition useArray inpt := 
input <- $$ inpt;:
"arraySize" <- new $$ (1);:
##("arraySize")%expr [$$ (0) ]*<- ##(input);:
(Syntax.ReadAt output (##"arraySize")%expr ($$ 0)%expr).

Lemma Safe_useArray: forall W, Safety.Safe functions (useArray W) v.
  solve_safe.

  unfold safe_access.
  updSimpl; rewriter.
  split; variables.
  
  unfold safe_access.
  rewriter_clear.
  updSimpl.
Qed.

Lemma Correct_useArray: forall w, forall st st', RunsTo functions (useArray w) st st' -> Output st' = w.
  solve_correct.
  updSimpl; rewriter; updSimpl.
  nomega.
  variables.
Qed.
End UseArrayProg.

Section UseCondProg.
Variable functions : W -> option (Callee).
Variable v: st.

Definition positive var:= ($$ 0 .< ## var)%expr. 
Transparent positive.
Print positive.
Locate "While".
Close Scope SP_scope.
Definition useCond inpt := 
  input <- $$ inpt ;:
  inCase (positive input) {{
    output <- $$ (1)
  }}else{{
    output <- $$ (0)
  }}.

Print useCond.

Lemma Safe_useCond: forall w, Safety.Safe functions (useCond w) v.
  unfold useCond.
  destruct w;
  solve_safe.
Qed.

Definition positiveDenote (w:W):=
  if (weq $0 w) then 0 else 1. 
  
Transparent positiveDenote.

Ltac conditions:= rewrite wltb_geq; [ | auto ]; rewrite wneb_eq; auto.

Lemma ne_lt: forall w sz, natToWord sz 0 <> (natToWord sz w) -> (natToWord sz 0 < (natToWord sz w))%word.
Admitted.

Lemma Correct_useCond: forall w, forall st st', RunsTo functions (useCond w) st st' -> Output st' = positiveDenote w.
  intro w.
  simpl; solve_correct; auto; unfold positiveDenote; destruct weq; try reflexivity.

  contradict H6; updSimpl; conditions.
  contradict H6; updSimpl; apply ne_lt in n.
  rewrite wltb_lt; auto; rewrite wneb_ne; discriminate.
Qed.

End UseCondProg.

Section UseLoopProg.
Variable functions : W -> option (Callee).
Variable v: st.

Print Statement.

Definition theLoop :=While (e_lt "i" input) {{ ("temp" .++);:("i" .++)}}.
Transparent theLoop.
Definition useLoop inpt := 
  input <- $$ inpt ;:
  "temp" <- $$ 2 ;:
  "i" <- $$ 0 ;:
  theLoop;:
  output <- ##"temp".

Lemma Safe_theLoop: forall v, Safety.Safe functions theLoop v.
  unfold theLoop; cofix;
  solve_safe.
Qed.

Hint Resolve Safe_theLoop.

Lemma Safe_useLoop: Safety.Safe functions (useLoop 1) v.
 solve_safe.
Qed.

Print theLoop.

Definition theLoopInvariant n (s:st):=
  fst s input = n
  /\ (fst s "i" <= n)%word
  /\ fst s "temp" = fst s "i" ^+ $2
  /\ fst s input = n.

Set Implicit Arguments.


Lemma Correct_theLoop: forall n, forall st st', 
  RunsTo functions theLoop st st' -> 
  theLoopInvariant n st ->
 (fst st' "i" = n)%word /\ theLoopInvariant n st'.
  intros.
  use_loop_inv (theLoopInvariant n); unfold theLoopInvariant in *.
  repeat openHyp; descend.
  unfold e_lt in *; wltb; subst.
  apply wordToNat_inj; nomega.

  simpl; intros; repeat openHyp;
  solve_correct; intuition (subst; unfold input in *; simpl in *).
  wltb.
  pre_nomega.
  rewrite <- (next _ _ (vs0 "input")) in H; nomega.
  rewriter_clear.
  repeat rewrite <- wplus_assoc; f_equal; nomega.
Qed.

Lemma Correct_useloop: forall n, forall st st', 
  RunsTo functions (useLoop n) st st' -> 
  Output st' = ($ n ^+ $ 2).
  solve_correct_with theLoop.
  eapply Correct_theLoop in H5;
  unfold theLoopInvariant in *; simpl in *; 
    updSimpl; repeat openHyp; repeat split; auto.
  intuition.
  pre_nomega; change (wordToNat $ (0)) with 0; omega.
Qed.

End UseLoopProg.