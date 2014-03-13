Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import ProgramLogic2.
  Module Import ProgramLogicMake := Make E.

  Require Import AutoSep.
  Require Import Syntax.
  Require Import SyntaxExpr Memory IL String.
  Require Import Notations3.

  Local Open Scope expr.

  Infix ";;" := SeqEx : stmtex_scope.

  Delimit Scope stmtex_scope with stmtex.

  Notation "'skip'" := SkipEx : stmtex_scope.

  Notation "'BEFORE' ( vs , h ) 'AFTER' ( vs' , h' ) p" :=
    (fun _ s s' => let vs := sel (fst s) in let h := snd s in let vs' := sel (fst s') in let h' := snd s' in
      p%word) (at level 0, p at level 200) : stmtex_inv_scope.

  Delimit Scope stmtex_inv_scope with stmtex_inv.

  Notation "[ inv ] 'While' cond { body }" := (WhileEx inv%stmtex_inv cond%expr body) : stmtex_scope.

  Notation "'If' cond { trueStmt } 'else' { falseStmt }" := (IfEx cond%expr trueStmt falseStmt) : stmtex_scope.

  Notation "x <- e" := (AssignEx x e%expr) : stmtex_scope.

  Notation "'Assert' [ p ]" := (AssertEx p%stmtex_inv) : stmtex_scope.

  Notation "'DCall' f ()" := (DCallEx None f nil)
                               (no associativity, at level 95, f at level 0) : stmtex_scope.

  Notation "'DCall' f ( x1 , .. , xN )" := (DCallEx None f (@cons Expr x1 (.. (@cons Expr xN nil) ..))%expr)
                                             (no associativity, at level 95, f at level 0) : stmtex_scope.

  Notation "x <-- 'DCall' f ()" := (DCallEx (Some x) f nil)
                                     (no associativity, at level 95, f at level 0) : stmtex_scope.

  Notation "x <-- 'DCall' f ( x1 , .. , xN )" := (DCallEx (Some x) f (@cons Expr x1 (.. (@cons Expr xN nil) ..))%expr) (no associativity, at level 95, f at level 0) : stmtex_scope.

  Notation "a ! b" := (a, b) (only parsing) : stmtex_scope.

  Local Close Scope expr.

  Ltac selify :=
    repeat match goal with
             | [ |- context[upd ?a ?b ?c ?d] ] => change (upd a b c d) with (sel (upd a b c) d)
             | [ |- context[fst ?X ?S] ] => change (fst X S) with (sel (fst X) S)
           end.

  Ltac unfold_all :=
    repeat match goal with
             | H := _ |- _ => unfold H in *; clear H
           end.

  Ltac cito' :=
    repeat (subst; simpl; selify; autorewrite with sepFormula in *;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end).

  Require Import SyntaxFunc GeneralTactics.
  Import SemanticsMake FuncCore ProgramLogicMake.

  Ltac cito_vcs body := unfold body; simpl;
    unfold imply_close, and_lift, interp; simpl;
      firstorder cito'; auto.

  Ltac solve_vcs vcs_good :=
    match goal with 
      | |- and_all _ _ => eapply vcs_good 
      | |- _ => idtac 
    end.

  Ltac cito_runsto f pre vcs_good := 
    intros;
    match goal with
      | [ H : _ |- _ ] => 
        unfold f, Body, Core in H;
          eapply sound_runsto' with (p := pre) (s := Body f) in H; 
          solve_vcs vcs_good
          ; simpl in *;
          auto; openhyp; subst; simpl in *; unfold pre, and_lift, or_lift in *; openhyp
    end.

  Ltac cito_safe f pre vcs_good := 
    intros;
    unfold f, Body, Core; eapply sound_safe with (p := pre); 
    solve_vcs vcs_good
    ; simpl in *; try unfold pre in *; unfold pre, imply_close, and_lift in *; simpl in *;
    auto; openhyp; subst; simpl in *.

  Theorem lt0_false : forall (n : string) env v v',
    is_false (0 < n)%expr env v v'
    -> ($0 >= sel (fst v') n)%word.
    intros.
    hnf in H.
    simpl in H.
    unfold wltb in H.
    destruct (wlt_dec (natToW 0) (fst v' n)); try discriminate; auto.
  Qed.

  Theorem lt0_true : forall (n : string) env v v',
    is_true (0 < n)%expr env v v'
    -> ($0 < sel (fst v') n)%word.
    intros.
    hnf in H.
    simpl in H.
    unfold wltb in H.
    destruct (wlt_dec (natToW 0) (fst v' n)); try tauto; auto.
  Qed.

  Hint Immediate lt0_false lt0_true.

  Import List.

  Lemma map_length_eq : forall A B ls1 ls2 (f : A -> B), List.map f ls1 = ls2 -> length ls1 = length ls2.
    intros.
    eapply f_equal with (f := @length _) in H.
    simpl in *; rewrite map_length in *; eauto.
  Qed.

  Import Semantics.
  Import SemanticsMake.

  Fixpoint make_triples_2 words (in_outs : list (ArgIn * ArgOut)) :=
    match words, in_outs with
      | p :: ps, o :: os => {| Word := p; ADTIn := fst o; ADTOut := snd o |} :: make_triples_2 ps os
      | _, _ => nil
    end.

  Lemma triples_intro : forall triples words in_outs, words = List.map (@Word _) triples -> List.map (fun x => (ADTIn x, ADTOut x)) triples = in_outs -> triples = make_triples_2 words in_outs.
    induction triples; destruct words; destruct in_outs; simpl in *; intuition.
    f_equal; intuition.
    destruct a; destruct p; simpl in *.
    injection H; injection H0; intros; subst.
    eauto.
  Qed.

  Ltac inversion_Forall :=
    repeat match goal with
             | H : List.Forall _ _ |- _ => inversion H; subst; clear H
           end.

End Make.
