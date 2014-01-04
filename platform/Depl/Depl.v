(** * Logical expression notations *)

Require Import Depl.Logic.

Notation "!" := Dyn.

Definition Var' : string -> expr := Var.
Coercion Var' : string >-> expr.

Notation "|^ fE , e |" := (Lift (fun fE => e)) (fE at level 0) : expr_scope.
Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.


(** * Predicate notations *)

Notation "|^ fE , P |" := (Pure (fun fE => P%type)) (fE at level 0) : pred_scope.

Delimit Scope pred_scope with pred.
Bind Scope pred_scope with pred.

Infix "*" := Star : pred_scope.
Notation "'EX' x , p" := (Exists x p%pred) (at level 89) : pred_scope.
Notation "'Emp'" := (Pure (fun _ => True)) : pred_scope.



(** * Program expression notations *)

Require Import Depl.Statements.

Definition Var'' : string -> expr := Var.
Coercion Var'' : string >-> expr.
Coercion Const : W >-> expr.


(** * Program statement notations *)

Infix "<-" := Assign : stmt_scope.
Infix ";;" := Seq : stmt_scope.
Notation "'Return' e" := (Ret e) : stmt_scope.

Delimit Scope stmt_scope with stmt.
Bind Scope stmt_scope with stmt.


(** * Program function spec notations *)

Record fspec := {
  SpecVars_ : list fo_var;
  Formals_ : list pr_var;
  Precondition_ : pred;
  Postcondition_ : pred
}.

Notation "'PRE' pre 'POST' post" := {| SpecVars_ := nil;
  Formals_ := nil;
  Precondition_ := pre%pred;
  Postcondition_ := post%pred
|} (at level 88) : spec_scope.

Notation "'ARGS' () s" := s (at level 89) : spec_scope.

Notation "'ARGS' ( x1 , .. , xN ) s" := {| SpecVars_ := nil;
  Formals_ := cons x1 (.. (cons xN nil) ..);
  Precondition_ := Precondition_ s;
  Postcondition_ := Postcondition_ s
|} (at level 89) : spec_scope.

Notation "'AL' x , s" := {| SpecVars_ := x :: SpecVars_ s;
  Formals_ := Formals_ s;
  Precondition_ := Precondition_ s;
  Postcondition_ := Postcondition_ s
|} (at level 89, x at level 0) : spec_scope.

Delimit Scope spec_scope with spec.
Bind Scope spec_scope with fspec.


(** * Program function notations *)

Record func := {
  Name_ : string;
  Spec_ : fspec;
  Locals_ : list pr_var;
  Body_ : stmt
}.

Notation "'dfunction' name [ p ] b 'end'" := {|
  Name_ := name;
  Spec_ := p%spec;
  Locals_ := nil;
  Body_ := b%stmt
|} (no associativity, at level 95, name at level 0, only parsing) : func_scope.

Notation "'dfunction' name [ p ] 'Locals' x1 , .. , xN ;; b 'end'" := {|
  Name_ := name;
  Spec_ := p%spec;
  Locals_ := cons x1 (.. (cons xN nil) ..);
  Body_ := b%stmt
|} (no associativity, at level 95, name at level 0, only parsing) : func_scope.

Delimit Scope func_scope with func.


(** * Program module notations *)

Require Import Depl.CompileModule.

Definition funcOut (f : func) : function := {|
  Name := Name_ f;
  SpecVars := SpecVars_ (Spec_ f);
  Formals := Formals_ (Spec_ f);
  Locals := Locals_ f;
  Precondition := Precondition_ (Spec_ f);
  Postcondition := Postcondition_ (Spec_ f);
  Body := Body_ f
|}.

Notation "{{ x 'with' .. 'with' y }}" := (cons x%func .. (cons y%func nil) ..) (only parsing) : funcs_scope.
Delimit Scope funcs_scope with funcs.

Notation "'dmodule' name fs" := (compileModule {| MName := name;
  Functions := map funcOut fs%funcs |})
  (no associativity, at level 95, name at level 0, only parsing).


(** * Tactics *)

Ltac depl_cbv := cbv beta iota zeta delta [CompileModule.makeVcs CompileModule.Functions map funcOut
  CompileModule.functionVc CompileModule.Postcondition Statements.stmtV
  CompileModule.Formals
  SpecVars_ Formals_ Precondition_ Postcondition_
  Name_ Spec_ Locals_ Body_ Logic.wellScoped CompileModule.Body
  Logic.normalize Statements.stmtD CompileModule.Precondition app
  CompileModule.Locals Statements.sentail Statements.exprV Statements.exprD
  Cancel.cancel Cancel.findMatchings Logic.NQuants Logic.NImpure Logic.NPure
  Logic.nsubst CompileModule.SpecVars Cancel.findMatching Logic.predExt].

Ltac depl_wf :=
  match goal with
    | [ H : forall x : Logic.fo_var, _ -> _ x = _ x |- _ ] =>
      unfold Logic.fo_set; simpl;
        repeat rewrite H by (discriminate || (simpl; tauto)); reflexivity
  end.

Ltac depl := apply CompileModule.compileModule_ok; [
  constructor
  | reflexivity
  | depl_cbv;
    match goal with
      | [ |- vcs ?Ps ] => apply (vcsImp_correct Ps)
    end; intuition; try depl_wf; unfold Logic.fo_set; simpl ].
