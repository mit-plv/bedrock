Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Semantics.
  Module Import SemanticsMake := Make E.

  Section TopSection.

    Require Import Syntax.
    Require Import AutoSep.

    (* shallow embedding *)
    Definition assert := State -> Prop.
    Definition interp (p : assert) (s : State) : Prop := p s.
    Definition abs (f : State -> Prop) : assert := f.

    Inductive StmtEx := 
    | SkipEx : StmtEx
    | SeqEx : StmtEx -> StmtEx -> StmtEx
    | IfEx : Expr -> StmtEx -> StmtEx -> StmtEx
    | WhileEx : assert -> Expr -> StmtEx -> StmtEx
    | AssignEx : string -> Expr -> StmtEx
    | AssertEx : assert -> StmtEx.

    Definition and_lift (a b : assert) : assert := abs (fun s => interp a s /\ interp b s).
    Definition or_lift (a b : assert) : assert := abs (fun s => interp a s \/ interp b s).
    Definition imply_close (a b : assert) : Prop := forall s, interp a s -> interp b s.

    Infix "/\" := and_lift : assert_scope.
    Infix "\/" := or_lift : assert_scope.
    Infix "-->" := imply_close (at level 90) : assert_scope.

    Require Import SemanticsExpr.

    Close Scope equiv_scope.

    Definition is_true e : assert := abs (fun s => eval (fst s) e <> $0).
    Definition is_false e : assert := abs (fun s => eval (fst s) e = $0).

    Open Scope assert_scope.

    Fixpoint sp (stmt : StmtEx) (p : assert) : assert :=
      match stmt with
        | SkipEx => p
        | SeqEx a b => sp b (sp a p)
        | IfEx e t f => sp t (p /\ is_true e) \/ sp f (p /\ is_false e)
        | WhileEx inv e _ => inv /\ is_false e
        | AssignEx x e => 
          abs (fun s => 
                 exists w, 
                   let s' := (upd (fst s) x w, snd s) in
                   interp p s' /\
                   sel (fst s) x = eval (fst s') e)%type
        | AssertEx a => a
      end.

    Fixpoint vc stmt (p : assert) : list Prop :=
      match stmt with
        | SkipEx => nil
        | SeqEx a b => vc a p ++ vc b (sp a p)
        | IfEx e t f => vc t (p /\ is_true e) ++ vc f (p /\ is_false e)
        | WhileEx inv e body => 
          (p --> inv) :: (sp body (inv /\ is_true e) --> inv) :: vc body (inv /\ is_true e)
        | AssignEx x e => nil
        | AssertEx a => (p --> a) :: nil
      end.
    
    Fixpoint to_stmt s :=
      match s with
        | SkipEx => Syntax.Skip
        | SeqEx a b => Syntax.Seq (to_stmt a) (to_stmt b)
        | IfEx e t f => Syntax.If e (to_stmt t) (to_stmt f)
        | WhileEx _ e b => Syntax.While e (to_stmt b)
        | AssignEx x e => Syntax.Assign x e
        | AssertEx _ => Syntax.Skip
      end.

    Coercion to_stmt : StmtEx >-> Stmt.

    Definition and_all := fold_right and True.

    Require Import GeneralTactics.

    Lemma and_all_app : forall ls1 ls2, and_all (ls1 ++ ls2) -> and_all ls1 /\ and_all ls2.
      induction ls1; simpl; intuition.
      eapply IHls1 in H1; openhyp; eauto.
      eapply IHls1 in H1; openhyp; eauto.
    Qed.

    Lemma is_true_intro : forall e v, wneb (eval (fst v) e) $0 = true -> interp (is_true e) v.
      intros.
      unfold is_true.
      unfold interp, abs.
      unfold wneb in *.
      destruct (weq _ _) in *; intuition.
    Qed.

    Hint Resolve is_true_intro.

    Lemma is_false_intro : forall e v, wneb (eval (fst v) e) $0 = false -> interp (is_false e) v.
      intros.
      unfold is_false.
      unfold interp, abs.
      unfold wneb in *.
      destruct (weq _ _) in *; intuition.
    Qed.

    Hint Resolve is_false_intro.

    Theorem sound' : forall env (s : Stmt) v v', RunsTo env s v v' -> forall s' : StmtEx, s = s' -> forall p, and_all (vc s' p) -> interp p v -> interp (sp s' p) v'.
      induction 1; simpl; intros; destruct s'; try discriminate; simpl in *; try (injection H1; intros; subst).

      (* skip *)
      eauto.

      openhyp.
      eauto.

      (* seq *)
      eapply and_all_app in H2; openhyp.
      eauto.

      (* if *)
      eapply and_all_app in H2; openhyp.
      left.
      eapply IHRunsTo; eauto.
      split; eauto.

      eapply and_all_app in H2; openhyp.
      right.
      eapply IHRunsTo; eauto.
      split; eauto.

      (* while *)
      openhyp.
      subst loop.
      injection H2; intros; subst.
      eapply (IHRunsTo2 (WhileEx _ e s')); simpl in *; eauto.
      eapply IHRunsTo1; simpl in *; eauto.
      split; eauto.

      openhyp.
      subst loop.
      injection H0; intros; subst.
      split; eauto.

      (* assign *)
      subst vs.
      injection H; intros; subst.
      unfold interp, abs.
      destruct v; simpl in *.
      eexists (sel v s).
      replace (upd _ _ _) with v in *.
      split.
      eauto.
      repeat rewrite sel_upd_eq by eauto; eauto.
      Require Import FunctionalExtensionality.
      extensionality x.
      change (upd (upd v s (eval v e0)) s (sel v s) x) with (sel (upd (upd v s (eval v e0)) s (sel v s)) x).
      destruct (string_dec x s).
      subst.
      repeat rewrite sel_upd_eq by eauto; eauto.
      repeat rewrite sel_upd_ne by eauto; eauto.
    Qed.

    Theorem sound : forall env (s : StmtEx) v v', RunsTo env s v v' -> forall p, and_all (vc s p) -> interp p v -> interp (sp s p) v'.
      intros.
      eapply sound'; eauto.
    Qed.

  End TopSection.

End Make.