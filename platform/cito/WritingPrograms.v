(*Require Import MyMalloc MyFree.*)
Require Import GeneralTactics VariableLemmas.
Require Import SyntaxExpr SemanticsExpr CompileExpr.
Require Import Semantics Safety CompileStatement SemanticsLemmas Syntax.
Export SyntaxExpr.

Set Implicit Arguments.

Close Scope SP_scope.
(*Introduce Notation*)
(**Remember old notation:*
Infix ";:" := Syntax.Seq (left associativity, at level 110).
Infix "<-" := Syntax.Assignment (at level 90, no associativity).
Notation "var <- 'new' size" := (Syntax.Malloc var size) (no associativity, at level 60).
Notation "a [ i ] *<- e" := (Syntax.WriteAt a i e) (at level 60).
Notation skip := Syntax.Skip.
Notation delete := Syntax.Free.
*)

Coercion Const : W >-> Expr.
Coercion Var : string >-> Expr.

Infix "+" := (Binop Plus) : expr_scope.
Infix "-" := (Binop Minus) : expr_scope.
Infix "*" := (Binop Times) : expr_scope.
Infix "=" := (TestE IL.Eq) : expr_scope.
Infix "<>" := (TestE IL.Ne) : expr_scope.
Infix "<" := (TestE IL.Lt) : expr_scope.
Infix "<=" := (TestE IL.Le) : expr_scope.

Notation "var <== a [ i ]" := (ReadAt var a%expr i%expr) (at level 60, a at level 0, i at level 0): stmnt_scope.
Notation "'inCase' ( cond ) {{ trueStmnt }} 'else' {{ falseStmnt }}" := (Conditional cond%expr trueStmnt falseStmnt) (no associativity, at level 55, format 
 "'[hv' 'inCase'  ( cond )  {{ '/  ' trueStmnt '/' '}}' 'else' {{ '/  ' falseStmnt '/' }} ']'"): stmnt_scope.
Notation "'While' ( cond ) {{ body }}" := (Loop cond%expr body) (no associativity, at level 55, format 
 "'[hv' 'While'  ( cond )  {{ '/  ' body '/' '}}' ']'"): stmnt_scope.

Notation "'If' cond { trueStmnt } 'else' { falseStmnt }" := (Conditional cond%expr trueStmnt falseStmnt)
  : stmnt_scope.

Notation "'Call' f [ arg ]" := (Syntax.Call f arg)
  (no associativity, at level 95, f at level 0) : stmnt_scope.

Infix ";;" := Syntax.Seq : stmnt_scope.

(*Redefine the notations:*)
Notation "x ;: y" := (Syntax.Seq x y) (left associativity, at level 110, format " x ;: '/' y"): stmnt_scope.
Notation "var <- expr " := (Syntax.Assignment var expr%expr) (at level 90, no associativity): stmnt_scope.
Notation "var <- 'new' size" := (Syntax.Malloc var size%expr) (no associativity, at level 60): stmnt_scope.
Notation "a [ i ] <== e" := (Syntax.WriteAt a%expr i%expr e%expr) (at level 60): stmnt_scope.

Delimit Scope stmnt_scope with stmnt.
Open Scope stmnt.


Definition add1 input:= (##input .+ $$ 1)%expr.
Definition subst1 input:= (##input .- $$ 1)%expr.

Transparent add1 subst1.


Notation " var '.++'" := (Syntax.Assignment var (add1 var)) (at level 111): stmnt_scope.
Notation " var '.--'" := (Syntax.Assignment var (subst1 var)) (at level 111): stmnt_scope.

Definition ForFromTo (i:string) (from: Expr) (to:Expr) body :=
  (i <- from);:
  While ( (## i) .< to) {{
    body;:(i.++)
  }}.

Notation "'For' i 'from' from 'to' to {{ body }}" := (ForFromTo i from to body) (no associativity, at level 55, format 
 "'[hv' 'For' i 'from' from 'to' to  {{ '/  ' body '/' '}}' ']'"): stmnt_scope.

Definition ForTo (i:string) (To: Expr) body :=
  (i <- $$ 0);:
  While ( (## i) .< To) {{
    body;: (i.++)
  }}.


(* Tactics *)

Lemma wordToNat_inj : forall u w : W,
  wordToNat u = wordToNat w
  -> u = w.
  intros.
  apply (f_equal natToW) in H.
  unfold natToW in *.
  repeat rewrite natToWord_wordToNat in *; auto.
Qed.

Lemma wltb_1 : forall u w : W,
  ((if wltb u w then $1 else $0) = natToW 0 -> False)
  -> (u < w)%word.
  intros; destruct (wlt_dec u w); auto.
  apply wltb_geq in n; rewrite n in *; tauto.
Qed.

Lemma wltb_0 : forall u w : W,
  (if wltb u w then $1 else $0) = natToW 0
  -> (u >= w)%word.
  intros; destruct (wlt_dec u w); auto.
  apply wltb_lt in w0; rewrite w0 in *; discriminate.
Qed.


Ltac wltb :=
  repeat match goal with
           | [ H : _ -> False |- _ ] => apply wltb_1 in H
           | [ H : _ = _ |- _ ] => apply wltb_0 in H
         end.

Lemma wneb_true_fwd : forall u w : W,
  wneb u w = true
  -> u <> w.
  intros; destruct (weq u w); auto.
  apply wneb_eq in e; congruence.
Qed.

Lemma wneb_false_fwd : forall u w : W,
  wneb u w = false
  -> u = w.
  intros; destruct (weq u w); auto.
  apply wneb_ne in n; congruence.
Qed.

Hint Immediate wneb_true_fwd wneb_false_fwd.
Lemma use_loop_invariant' : forall functions cond body (inv : st -> Prop) loop s s',
  RunsTo functions loop s s'
  -> loop = While (cond) {{ body }}
  -> inv s
  -> (forall s s', inv s
    -> exprDenote cond (fst s) <> $0
    -> RunsTo functions body s s'
    -> inv s')
  -> exprDenote cond (fst s') = $0 /\ inv s'.
  induction 1; intros; subst; try discriminate;
    match goal with
      | [ H : While (_) {{_}} = While (_) {{_}} |- _ ] => inversion H; clear H; subst
    end; eauto.
Qed.
  
Lemma use_loop_invariant : forall functions (inv : st -> Prop) cond body s s',
  RunsTo functions (While (cond) {{ body }}) s s'
  -> inv s
  -> (forall s s', inv s
    -> exprDenote cond (fst s) <> $0
    -> RunsTo functions body s s'
    -> inv s')
  -> exprDenote cond (fst s') = $0 /\ inv s'.
  intros; eauto using use_loop_invariant'.
Qed.

Ltac use_loop_inv inv:= intros;
  match goal with
    | H:  RunsTo _ _ _ _ |- _ => eapply (@use_loop_invariant _ (inv)) in H; [ | eassumption | clear]
  end.


Ltac c := constructor; intros.

Ltac invert_safe :=
  match goal with
    | [ |- Safety.Safe _ (While (?cond) {{ _ }}) ?s ] =>
      let H := fresh "H" in
        case_eq (wneb (exprDenote cond (fst s)) ($0)%word); intro;
          (apply Safety.LoopTrue; [ assumption | | ])
          || (apply Safety.LoopFalse; assumption); intros
    | [ |- Safety.Safe ?functions (inCase ( ?cond ) {{ _ }}else{{ _ }}) ?s ] =>
        case_eq (wneb (exprDenote cond (fst s)) ($0)%word); intro;
          (apply Safety.ConditionalTrue; [ assumption | ])
          || (apply Safety.ConditionFalse; [assumption | ]); intros
  end.

Ltac open_state:=
  match goal with
    | |- Safety.Safe _ ?stmnt (_ , _) => idtac
    | |- Safety.Safe _ ?stmnt ?v => destruct v; simpl
  end.

Ltac safe1 := intros; open_state; (invert_safe || c).

Ltac evalRTwith respect:=
  repeat match goal with
           | [ H : RunsTo _ _ ?E _ |- _ ] =>
             match E with
               | respect => fail 1
               | _ => inversion H; clear H; repeat match goal with
                                                     | [ x : _ |- _ ] => subst x
                                                   end
             end
         end. 

Ltac evalRT:= 
  repeat match goal with
           | [ H : RunsTo _ _ ?E _ |- _ ] =>
             match E with
               | While (_) {{ _ }} => fail 1
               | _ => inversion H; clear H; repeat match goal with
                                                     | [ x : _ |- _ ] => subst x
                                                   end
             end
         end.

Ltac solve_safe := safe1; repeat (auto; safe1; evalRT).

Ltac solve_correct_with respect:= intros; evalRTwith respect; unfold upd, sel; simpl.

Ltac solve_correct:= intros; evalRT; unfold upd, sel; simpl.


Lemma upd_eq: forall (vs : vals) (nm : string) (v : W) (nm' : string),
       nm = nm' -> (upd vs nm v) nm' = v.
  eapply sel_upd_eq.
Qed.

Lemma upd_ne: forall (vs : vals) (nm : string) (v : W) (nm' : string),
       nm <> nm' -> (upd vs nm v) nm' = vs nm'.
  eapply sel_upd_ne.
Qed.
Ltac compare_strings:= eauto.
Ltac compare_keys:= eauto.

(*Ill put the hints in a tactics while I get how to solve the subgoals.*)
Ltac updSimpl:= unfold upd, sel;
  simpl;
  repeat (first [ 
     rewrite upd_length
    | rewrite sel_upd_eq 
    | rewrite sel_upd_ne 
    | rewrite upd_sel_equiv
    | rewrite WDict.sel_upd_eq
    | rewrite WDict.sel_upd_ne
    | rewrite ExprLemmas.sel_upd ]; auto).


(*Common definitions*)


Definition output:= "outout".
Definition input:= "input".

Function getVar var (v:st):= sel (fst v) var.
Definition Output v:= getVar output v.
Function getArray key (v:st):= snd (snd v) key.

Definition e_lt a b:= SyntaxExpr.TestE IL.Lt (SyntaxExpr.Var a )(SyntaxExpr.Var b).
