(** Statements of the deeply embedded programming language *)

Require Import AutoSep.

Require Import Depl.Logic Depl.Cancel Depl.AlgebraicDatatypes.


(** * Syntax *)

(** Type synonym for program variables *)
Definition pr_var := string.

(** Side-effect-free expressions *)
Inductive expr :=
| Const (w : W)
| Var (x : pr_var).

(** Side-effecting statements *)
Inductive stmt :=
| Assign (x : pr_var) (e : expr)
| Seq (s1 s2 : stmt)
| Ret (e : expr).

(** Function definitions *)
Record fncn := {
  ArgumentVariables : list pr_var;
  (** Function formal arguments *)
  LocalVariables : list pr_var;
  (** These variables are available as scratch space. *)
  SpecVariables : list fo_var;
  (** Additionally, consider these variables quantified over the whole function spec. *)
  Precondition : pred;
  (** Holds when function is called. *)
  Body : stmt;
  (** Run this code when the function is called. *)
  Postcondition : pred
  (** Holds upon function return (with spec variable "result" available). *)
}.

(** ** Syntactic validity *)

Section validity.
  Variable variables : list pr_var.

  Definition exprV (e : expr) :=
    match e with
      | Const _ => True
      | Var x => In x variables
    end.

  Fixpoint stmtV (s : stmt) :=
    match s with
      | Assign x e => In x variables /\ exprV e
      | Seq s1 s2 => stmtV s1 /\ stmtV s2
      | Ret e => exprV e
    end.
End validity.

Definition fncnV (f : fncn) := stmtV (ArgumentVariables f ++ LocalVariables f) (Body f).


(** * Semantics *)

(** Symbolic state, mapping program variables to logical expressions *)
Definition vars := pr_var -> option Logic.expr.

Definition vars_set (vs : vars) (x : pr_var) (e : Logic.expr) : vars := 
  fun y => if string_dec y x then Some e else vs y.

(** When does a [vars] agree with a [vals] (from the main Bedrock library)? *)
Definition vars_ok (fE : fo_env) (V : vals) (vs : vars) :=
  forall x e, vs x = Some e -> exprD e fE = Dyn (sel V x).

(** Initial symbolic state for the start of a function.
  * Each variable "x" is mapped to logical variable "x0". *)
Definition vars0 (locals : list pr_var) : vars :=
  fun x => if In_dec string_dec x locals then Some (Logic.Var (x ++ "0")%string) else None.

(** Translating program expressions to logical expressions *)
Definition exprD (vs : vars) (e : expr) : option Logic.expr :=
  match e with
    | Const w => Some (Lift (fun _ => Dyn w))
    | Var x => vs x
  end.

Inductive result :=
| ProveThis (P : Prop)
| Failed (P : Prop).

Inductive lhs_remains (p : list pred) := .

(** Strict entailment between normalized formulas,
  * where there may be no conjuncts left uncanceled on either side *)
Definition sentail (fvs : list fo_var) (lhs rhs : normal) :=
  match cancel fvs lhs rhs with
    | Success nil P => ProveThis P
    | Success lhs' _ => Failed (lhs_remains lhs')
    | Failure P => Failed P
  end.

Inductive bad_assignment_rhs (e : expr) := .
Inductive bad_assignment_lhs (x : pr_var) := .
Inductive bad_return_expr (e : expr) := .
Inductive entailment_failed_at_return (P : Prop) := .

(** Add a pure conjunct to a normalized predicate. *)
Definition addPure (n : normal) (P : fo_env -> Prop) : normal := {|
  NQuants := NQuants n;
  NPure := match NPure n with
             | None => Some P
             | Some P' => Some (fun fE => P' fE /\ P fE)
           end;
  NImpure := NImpure n
|}.

(** An axiomatic semantics for statements, via symbolic execution. *)
Section stmtD.
  Variable pre : normal.
  (** Precondition; holds throughout execution, since it describes the heap,
    * and there aren't yet heap-manipulating statements. *)
  Variable post : normal.
  (** Postcondition; check it at return points. *)

  Variable fvs : list fo_var.
  (** Logical variables legal to mention in specs (e.g., [pre]) *)

  (** Return a verification condition implying spec conformance. *)
  Fixpoint stmtD (vs : vars) (s : stmt)
    (k : vars -> Prop) (* Continuation; call when control falls through. *) : Prop :=
    match s with
      | Assign x e =>
        match exprD vs e with
          | None => bad_assignment_rhs e
          | Some e' =>
            match vs x with
              | None => bad_assignment_lhs x
              | Some _ => k (vars_set vs x e')
            end
        end
      | Seq s1 s2 =>
        stmtD vs s1 (fun vs' => stmtD vs' s2 k)
      | Ret e =>
        match exprD vs e with
          | None => bad_return_expr e
          | Some e' =>
            (** Build an extended precondition that records the return value. *)
            let pre' := nsubst "result" e' pre in

            match sentail ("result" :: fvs) pre' post with
              | ProveThis P => P
              | Failed P => entailment_failed_at_return P
            end
        end
    end.
End stmtD.
