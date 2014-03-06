Set Implicit Arguments.

Require Import ADT.

Module Make (Import E : ADT).

  Require Import Semantics.
  Module Import SemanticsMake := Make E.

  Section TopSection.

    Require Import Syntax Notations3.

    (* shallow embedding *)
    Definition assert := State -> Prop.
    Definition interp (p : assert) (s : State) : Prop := p s.
    Definition abs (f : State -> Prop) : assert := f.

    Inductive StmtEx := 
    | SkipEx : StmtEx
    | SeqEx : StmtEx -> StmtEx -> StmtEx
    | IfEx : Expr -> StmtEx -> StmtEx -> StmtEx
    | WhileEx : assert -> Expr -> StmtEx -> StmtEx
    | AssignEx : string -> Expr -> StmtEx.

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
      end.

    Fixpoint vc stmt (p : assert) : list Prop :=
      match stmt with
        | SkipEx => nil
        | SeqEx a b => vc a p ++ vc b (sp a p)
        | IfEx e t f => vc t (p /\ is_true e) ++ vc f (p /\ is_false e)
        | WhileEx inv e body => 
          (p --> inv) :: (sp body (inv /\ is_true e) --> inv) :: vc body (inv /\ is_true e)
        | AssignEx x e => nil
      end.
    
    Fixpoint to_stmt s :=
      match s with
        | SkipEx => Syntax.Skip
        | SeqEx a b => Syntax.Seq (to_stmt a) (to_stmt b)
        | IfEx e t f => Syntax.If e (to_stmt t) (to_stmt f)
        | WhileEx _ e b => Syntax.While e (to_stmt b)
        | AssignEx x e => Syntax.Assign x e
      end.

    Coercion to_stmt : StmtEx >-> Stmt.

    Definition and_all := fold_right and True.

    Theorem sound' : forall env (s : Stmt) v v', RunsTo env s v v' -> forall s' : StmtEx, s = s' -> forall p, and_all (vc s' p) -> interp p v -> interp (sp s' p) v'.
      induction 1; simpl; intros; destruct s'; try discriminate; simpl in *; try (injection H1; intros; subst).

      (* skip *)
      eauto.

      (* seq *)
      Lemma and_all_app : forall ls1 ls2, and_all (ls1 ++ ls2) -> and_all ls1 /\ and_all ls2.
        admit.
      Qed.
      Require Import GeneralTactics.
      eapply and_all_app in H2; openhyp.
      eauto.

      (* if *)
      eapply and_all_app in H2; openhyp.
      Lemma is_true_intro : forall e v, wneb (eval (fst v) e) $0 = true -> interp (is_true e) v.
        admit.
      Qed.
      Hint Resolve is_true_intro.
      Lemma is_false_intro : forall e v, wneb (eval (fst v) e) $0 = false -> interp (is_false e) v.
        admit.
      Qed.
      Hint Resolve is_false_intro.
      left.
      eapply IHRunsTo; eauto.
      split; eauto.

      eapply and_all_app in H2; openhyp.
      right.
      eapply IHRunsTo; eauto.
      split; eauto.

      (* while *)
      subst loop.
      injection H2; intros; subst.
      openhyp.
      (*here*)
      eapply IHRunsTo2.
      inversion H.
      subst loop0 loop1.
      subst.

    Qed.

    Theorem sound : forall env (s : StmtEx) v v', RunsTo env s v v' -> forall p, and_all (vc s p) -> interp p v -> interp (sp s p) v'.

  End TopSection.

End Make.