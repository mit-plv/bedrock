Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import ProgramLogic.
  Module Import ProgramLogicMake := Make E.

  Require Import AutoSep.
  Require Import Syntax.
  Require Import SyntaxExpr Memory IL String.
  Require Import Notations3.

  Local Open Scope expr.

  Infix ";;" := SeqEx : stmtex_scope.

  Notation "'skip'" := SkipEx : stmtex_scope.

  Notation "'BEFORE' ( vs , h ) 'AFTER' ( vs' , h' ) p" :=
    (fun s s' => let vs := sel (fst s) in let h := snd s in let vs' := sel (fst s') in let h' := snd s' in
      p%word) (at level 0, p at level 200) : stmtex_inv_scope.

  Delimit Scope stmtex_inv_scope with stmtex_inv.

  Notation "[ inv ] 'While' cond { body }" := (WhileEx inv%stmtex_inv cond%expr body) : stmtex_scope.

  Notation "'If' cond { trueStmt } 'else' { falseStmt }" := (IfEx cond%expr trueStmt falseStmt) : stmtex_scope.

  Notation "x <- e" := (AssignEx x e%expr) : stmtex_scope.

  Delimit Scope stmtex_scope with stmtex.

  Local Close Scope expr.

 
  Ltac selify :=
    repeat match goal with
             | [ |- context[upd ?a ?b ?c ?d] ] => change (upd a b c d) with (sel (upd a b c) d)
             | [ |- context[fst ?X ?S] ] => change (fst X S) with (sel (fst X) S)
           end.

  Ltac cito' :=
    repeat (subst; simpl; selify; autorewrite with sepFormula in *;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end).

  Require Import SyntaxFunc GeneralTactics.
  Import SemanticsMake FuncCore ProgramLogicMake.

  Ltac cito_vcs body := unfold body; simpl;
    unfold imply_close, and_lift, interp, abs; simpl;
      firstorder cito'; auto.

  Ltac cito_runsto f pre := intros;
    match goal with
      | [ H : _ _ _ _ _ |- _ ] => unfold f, Body, Core in H;
        eapply sound_runsto with (p := pre) in H;
          simpl in *; try unfold pre in *; unfold imply_close, and_lift, interp, abs in *; simpl in *;
            auto; openhyp; subst; simpl in *; intuition auto
    end.

  Ltac cito_safe f body pre := intros;
    unfold f, body, Body, Core; eapply sound_safe with (p := pre); [ reflexivity | .. ];
      simpl in *; try unfold pre in *; unfold imply_close, and_lift, interp, abs in *; simpl in *;
        auto; openhyp; subst; simpl in *; intuition auto.

  Theorem lt0_false : forall (n : string) v v',
    is_false (0 < n)%expr v v'
    -> ($0 >= sel (fst v') n)%word.
    intros.
    hnf in H.
    simpl in H.
    unfold wltb in H.
    destruct (wlt_dec (natToW 0) (fst v' n)); try discriminate; auto.
  Qed.

  Theorem lt0_true : forall (n : string) v v',
    is_true (0 < n)%expr v v'
    -> ($0 < sel (fst v') n)%word.
    intros.
    hnf in H.
    simpl in H.
    unfold wltb in H.
    destruct (wlt_dec (natToW 0) (fst v' n)); try tauto; auto.
  Qed.

  Hint Immediate lt0_false lt0_true.
End Make.
