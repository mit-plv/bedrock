(** * Logical expression notations *)

Require Import Depl.Logic Depl.CompileModule.

Module Make(Import M : LOGIC).
  Module Import CompileModule := CompileModule.Make(M).
  Export CompileModule.

Notation "!" := Dyn.
Notation "$ n" := (Word n).

Coercion Word : W >-> dyn.

Definition Var' : string -> Logic.expr := Logic.Var.
Coercion Var' : string >-> Logic.expr.

Notation "|^ fE , e |" := (Lift (fun fE => e)) (fE at level 0) : expr_scope.
Delimit Scope expr_scope with expr.
Bind Scope expr_scope with Logic.expr.

Definition wordbin' (f : W -> W -> W) (x y : dyn) : dyn :=
  match x, y with
    | Word x, Word y => Word (f x y)
    | _, _ => Word 0
  end.

Definition wordbin (f : W -> W -> W) (x y : Logic.expr) : Logic.expr :=
  Lift (fun fE => wordbin' f (Logic.exprD x fE) (Logic.exprD y fE)).

Definition eplus := wordbin (@wplus 32).
Definition eminus := wordbin (@wminus 32).
Definition emult := wordbin (@wmult 32).

Infix "^+" := eplus : expr_scope.
Infix "^-" := eminus : expr_scope.
Infix "^*" := emult : expr_scope.

Definition liftdyn (d : dyn) : Logic.expr :=
  Lift (fun _ => d).

Coercion liftdyn : dyn >-> Logic.expr.


(** * Predicate notations *)

Notation "|^ fE , P |" := (Pure (fun fE => P%type)) (fE at level 0) : pred_scope.

Delimit Scope pred_scope with pred.
Bind Scope pred_scope with pred.

Infix "*" := Star : pred_scope.
Notation "'EX' x , p" := (Exists x p%pred) (at level 89) : pred_scope.
Notation "'Emp'" := (Pure (fun _ => True)) : pred_scope.
Notation "e1 = e2" := (Equal e1%expr e2%expr) : pred_scope.
Notation "# X ( e1 , .. , eN )" := (Named X (@cons Logic.expr e1%expr (.. (@cons Logic.expr eN%expr nil) ..)))
  (X at level 0) : pred_scope.


(** * Program function spec notations *)

Import Statements.

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

Notation "'ARGS' ( x1 , .. , xN ) s" := {| SpecVars_ := SpecVars_ s;
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


(** * Program expression notations *)

Definition Var'' : string -> expr := Var.
Coercion Var'' : string >-> expr.
Coercion Const : W >-> expr.


(** * Program statement notations *)

Infix "<-" := Assign : stmt_scope.
Infix ";;" := Seq : stmt_scope.
Notation "'Return' e" := (Ret e) : stmt_scope.
Notation "x <-- # con ( e1 , .. , eN )" := (Allocate x con (@cons expr e1 (.. (@cons expr eN nil) ..)))
  (no associativity, at level 95, con at level 0) : stmt_scope.

Delimit Scope stmt_scope with stmt.
Bind Scope stmt_scope with stmt.


(** * Program function notations *)

Import AlgebraicDatatypes.

Record func := {
  Name_ : string;
  Spec_ : fspec;
  Locals_ : list pr_var;
  Body_ : stmt
}.

Inductive defn :=
  | Dtype (dt : datatype)
  | Func (fu : func).

Notation "'dfunction' name [ p ] b 'end'" := (Func {|
  Name_ := name;
  Spec_ := p%spec;
  Locals_ := nil;
  Body_ := b%stmt
|}) (no associativity, at level 95, name at level 0, only parsing) : func_scope.

Notation "'dfunction' name [ p ] 'Locals' x1 , .. , xN 'in' b 'end'" := (Func {|
  Name_ := name;
  Spec_ := p%spec;
  Locals_ := cons x1 (.. (cons xN nil) ..);
  Body_ := b%stmt
|}) (no associativity, at level 95, name at level 0, only parsing) : func_scope.

Delimit Scope func_scope with func.


(** * Datatype definition notations *)

Notation "# con ( nr1 , .. , nrN ; r1 , .. , rN ) p" := {|
  Name := con;
  Recursive := cons r1 (.. (cons rN nil) ..);
  Nonrecursive := cons nr1 (.. (cons nrN nil) ..);
  Condition := p%pred
|} (no associativity, at level 95, con at level 0) : con_scope.

Notation "# con ( ; r1 , .. , rN ) p" := {|
  Name := con;
  Recursive := cons r1 (.. (cons rN nil) ..);
  Nonrecursive := nil;
  Condition := p%pred
|} (no associativity, at level 95, con at level 0) : con_scope.

Notation "# con ( nr1 , .. , nrN ; ) p" := {|
  Name := con;
  Recursive := nil;
  Nonrecursive := cons nr1 (.. (cons nrN nil) ..);
  Condition := p%pred
|} (no associativity, at level 95, con at level 0) : con_scope.

Delimit Scope con_scope with con.
Bind Scope con_scope with con.

Notation "{{ x 'with' .. 'with' y }}" := (cons x%con .. (cons y%con nil) ..) (only parsing) : cons_scope.
Delimit Scope cons_scope with cons.

Notation "'dtype' name = cs" := (Dtype (name, cs%cons))
  (no associativity, at level 95, name at level 0, cs at level 0) : func_scope.


(** * Program module notations *)

Fixpoint separate (ds : list defn) : list datatype * list func :=
  match ds with
    | nil => (nil, nil)
    | Dtype dt :: ds =>
      let (dts, fs) := separate ds in
        (dt :: dts, fs)
    | Func fu :: ds =>
      let (dts, fs) := separate ds in
        (dts, fu :: fs)
  end.

Definition funcOut (f : func) : function := {|
  CompileModule.Name := Name_ f;
  CompileModule.SpecVars := SpecVars_ (Spec_ f);
  CompileModule.Formals := Formals_ (Spec_ f);
  CompileModule.Locals := Locals_ f;
  CompileModule.Precondition := Precondition_ (Spec_ f);
  CompileModule.Postcondition := Postcondition_ (Spec_ f);
  CompileModule.Body := Body_ f
|}.

Notation "{{ x 'with' .. 'with' y }}" := (cons x%func .. (cons y%func nil) ..) (only parsing) : funcs_scope.
Delimit Scope funcs_scope with funcs.

Notation "'dmodule' name ds" := (let (dts, fs) := separate ds%funcs in
                                 compileModule dts {| MName := name;
                                                      Functions := map funcOut fs |})
  (no associativity, at level 95, name at level 0, only parsing).


(** * Tactics *)

Ltac isConst E :=
  match E with
    | Ascii.Ascii _ _ _ _ _ _ _ _ => idtac
    | "" => idtac
    | String ?a ?ls => isConst a; isConst ls
    | @nil _ => idtac
    | ?a :: ?ls => isConst a; isConst ls
  end.

(* Simplify one of the syntactic well-formedness side conditions generated by [compileModule_ok]. *)
Ltac depl_wf :=
  match goal with
    | [ |- stmtV _ _ _ ] => simpl; tauto
    | [ |- Compile.datatypesWf _ ] =>
      repeat (econstructor; simpl in *; intros); simpl in *; intuition (try congruence);
        match goal with
          | [ H : forall x : Logic.fo_var, _ -> _ = _ |- _ ] =>
            repeat rewrite H by tauto; reflexivity
        end
    | [ |- forall fE fE' : Logic.fo_var -> Logic.dyn, (forall x, _ -> fE x = fE' x) -> _ = _ ] =>
      simpl; intros fE fE' Heq;
        repeat rewrite Heq by tauto; reflexivity
    | [ |- forall x : Logic.fo_var, _ -> _ <> None ] => simpl In; intuition (subst; simpl in *); congruence
    | [ |- forall fE : Logic.fo_env, List.Forall _ _ ] => intro;
      repeat match goal with
               | [ |- List.Forall _ _ ] => constructor
             end
    | [ |- forall fE fE' : Logic.fo_var -> Logic.dyn, (forall x, (if _ then _ else None) <> None -> fE x = fE' x)  -> _ = _ ] =>
      intros fE fE' Heq;
        repeat rewrite Heq by (simpl; congruence); reflexivity
    | [ |- In ?x ?ls ] => isConst x; isConst ls; simpl; tauto
    | [ |- forall x : Logic.fo_var, _ -> exists e : Logic.expr, _ ] =>
      simpl; intuition (subst; simpl; eauto)
    | [ |- forall fE fE' : Logic.fo_var -> Logic.dyn, _ -> forall e : Logic.expr, _ -> _ ] =>
      simpl; intuition (subst; auto)
    | [ |- forall fE1 fE2 : Logic.fo_var -> Logic.dyn,
             (forall x : Logic.fo_var, _ <> None -> fE1 x = fE2 x)
             -> _ = _ ] =>
      intros ? ? H; unfold Logic.fo_set; simpl;
      repeat rewrite H by (simpl; congruence); reflexivity
  end;
  try match goal with
        | [ |- Logic.exprD _ _ = Logic.exprD _ _ ] =>
          simpl; match goal with
                   | [ H : forall x : Logic.fo_var, _ |- _ ] => repeat rewrite H by tauto
                 end; reflexivity
      end.

Ltac depl' := apply CompileModule.compileModule_ok; [ constructor
  | hnf; NoDup
  | reflexivity
  | depl_wf
  | reflexivity
  |
  | simpl; discriminate ].

Ltac dsimpl := simpl; cbv delta [Logic.fo_set Cancel.fos_set]; simpl.

Ltac depl := depl'; dsimpl;
             match goal with
               | [ |- vcs ?Ps ] => apply (vcsImp_correct Ps)
             end;
             repeat match goal with
                      | [ |- _ /\ _ ] => split
                    end; repeat depl_wf; try tauto.

End Make.
