(** Statements of the deeply embedded programming language *)

Require Import Arith AutoSep.

Require Import Depl.Logic Depl.Cancel Depl.AlgebraicDatatypes.

Set Implicit Arguments.


Module Make(Import M : LOGIC).
  Module Import AlgebraicDatatypes := AlgebraicDatatypes.Make(M).
  Export AlgebraicDatatypes.

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
| Ret (e : expr)

(* Allocate an algebraic datatype value with a specific constructor and arguments. *)
| Allocate (x : pr_var) (conName : string) (args : list expr).

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

Section ForallF.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint ForallF (ls : list A) : Prop :=
    match ls with
      | nil => True
      | x :: ls' => P x /\ ForallF ls'
    end.

  Fixpoint ExistsF (ls : list A) : Prop :=
    match ls with
      | nil => False
      | x :: ls' => P x \/ ExistsF ls'
    end.
End ForallF.

Section validity.
  Variable dts : list ndatatype.

  Section variables.
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
        | Allocate x conName args => In x variables
          /\ ExistsF (fun dt => ExistsF (fun c => NName c = conName) (snd dt)) dts
          /\ ForallF exprV args
      end.
  End variables.

  Definition fncnV (f : fncn) := stmtV (ArgumentVariables f ++ LocalVariables f) (Body f).
End validity.


(** * Semantics *)

(** Symbolic state, mapping program variables to logical expressions *)
Definition vars := pr_var -> option Logic.expr.

Definition vars_set (vs : vars) (x : pr_var) (e : Logic.expr) : vars := 
  fun y => if string_dec y x then Some e else vs y.

(** When does a [vars] agree with a [vals] (from the main Bedrock library)? *)
Definition vars_ok (fE : fo_env) (V : vals) (vs : vars) :=
  forall x e, vs x = Some e -> exprD e fE = Word (sel V x).

(** Translating program expressions to logical expressions *)
Definition exprD (vs : vars) (e : expr) : option Logic.expr :=
  match e with
    | Const w => Some (Lift (fun _ => Word w))
    | Var x => vs x
  end.

(** Translating a sequence of expressions *)
Fixpoint exprsD (vs : vars) (es : list expr) : option (list Logic.expr) :=
  match es with
    | nil => Some nil
    | e :: es =>
      match exprD vs e, exprsD vs es with
        | Some e', Some es' => Some (e' :: es')
        | _, _ => None
      end
  end.

Inductive result :=
| ProveThis (P : Prop)
| Failed (P : Prop).

Inductive lhs_remains (p : list pred) := .

(** Strict entailment between normalized formulas,
  * where there may be no conjuncts left uncanceled on either side *)
Definition sentail (fvs : list fo_var) (lhs rhs : normal) :=
  match cancel fvs nil lhs rhs with
    | Success _ nil P => ProveThis P
    | Success _ lhs' _ => Failed (lhs_remains lhs')
    | Failure P => Failed P
  end.

Inductive bad_assignment_rhs (e : expr) := .
Inductive bad_assignment_lhs (x : pr_var) := .
Inductive bad_return_expr (e : expr) := .
Inductive entailment_failed_at_return (P : Prop) := .
Inductive unbound_constructor (s : string) := .
Inductive bad_constructor_argument (s : string) := .
Inductive wrong_number_of_constructor_arguments (s : string) := .
Inductive entailment_failed_at_allocation (P : Prop) := .
Inductive couldn't_determine_model (x : pr_var) := .
Inductive object_name_already_in_scope (x nextDt : pr_var) := .
Inductive datatype_constructor_variable_already_in_scope (x conName : pr_var) := .

(** Add a pure conjunct to a normalized predicate. *)
Definition addPure (n : normal) (P : fo_env -> Prop) : normal := {|
  NQuants := NQuants n;
  NPure := match NPure n with
             | None => Some P
             | Some P' => Some (fun fE => P' fE /\ P fE)
           end;
  NImpure := NImpure n
|}.

(** Find the datatype and definition corresponding to a constructor name. *)

Fixpoint lookupCon' (s : string) (cs : list ncon) : option ncon :=
  match cs with
    | nil => None
    | c :: cs' => if string_eq s (NName c) then Some c else lookupCon' s cs'
  end.

Fixpoint lookupCon (s : string) (dts : list ndatatype) : option (string * ncon) :=
  match dts with
    | nil => None
    | dt :: dts' =>
      match lookupCon' s (snd dt) with
        | None => lookupCon s dts'
        | Some c => Some (fst dt, c)
      end
  end.

(** An axiomatic semantics for statements, via symbolic execution. *)
Section stmtD.
  Variable dts : list ndatatype.
  (** Definitions of algebraic datatypes that may be referenced *)

  Variable ns : list pr_var.
  (** Program variables that are legal to assign to *)

  (** Return a verification condition implying spec conformance. *)
  Fixpoint stmtD (vs : vars)
    (fvs : list fo_var)
    (** Logical variables legal to mention in specs (e.g., [pre]) *)
    (pre : normal)
    (** Precondition; heap "right now" *)
    (post : normal)
    (** Postcondition; check it at return points. *)
    (nextDt : string)
    (** Next fresh name to use for a freshly allocated DT value *)
    (s : stmt)
    (k : vars -> list fo_var (* fvs *) -> normal (* pre *) -> normal (* post *)
      -> string (* nextDt *) -> Prop)
    (* Continuation; call when control falls through. *) : Prop :=
    match s with
      | Assign x e =>
        match exprD vs e with
          | None => bad_assignment_rhs e
          | Some e' =>
            if in_dec string_dec x ns
              then k (vars_set vs x e') fvs pre post nextDt
              else bad_assignment_lhs x
        end
      | Seq s1 s2 =>
        stmtD vs fvs pre post nextDt s1 (fun vs' fvs' pre' post' nextDt' =>
          stmtD vs' fvs' pre' post' nextDt' s2 k)
      | Ret e =>
        match exprD vs e with
          | None => bad_return_expr e
          | Some e' =>
            (* Build an extended postcondition that records the return value. *)
            let post' := nsubst "result" e' post in

            match sentail fvs pre post' with
              | ProveThis P => P
              | Failed P => entailment_failed_at_return P
            end
        end

      | Allocate x conName args =>
        (* Find the definition of this datatype constructor. *)
        match lookupCon conName dts with
          | None => unbound_constructor conName
          | Some (dtName, c) =>
            (* Check that the right number of arguments is passed. *)
            if eq_nat_dec (length args) (length (NRecursive c) + length (NNonrecursive c)) then
              (* Check for name clash between spec vars of current state & constructor defn. *)
              if notsInList fvs ("this" :: NRecursive c ++ NNonrecursive c
                                        ++ NQuants (NCondition c)) then
                (* Evaluate the constructor argument expressions. *)
                match exprsD vs args with
                  | None => bad_constructor_argument conName
                  | Some args' =>
                    (* Find a memory chunk to be absorbed inside this
                     * new DT object. *)
                    match cancel fvs ("this" :: nil)
                      pre (allocatePre dtName c args') with
                      | Failure P => entailment_failed_at_allocation P
                      | Success s lhs P =>
                        (* Look up the functional mode we've found. *)
                        match s "this" with
                          | None => couldn't_determine_model x
                          | Some model =>
                            (* Check if our chosen name for the new pointer
                             * is already used. *)
                            if in_dec string_dec nextDt fvs
                              then object_name_already_in_scope x nextDt
                              else
                                P /\
                                (* Use [nextDt] as the name of the new DT pointer. *)
                                k (vars_set vs x (Logic.Var nextDt))
                                (nextDt :: fvs)
                                {| NQuants := NQuants pre;
                                  NPure := NPure pre;
                                  NImpure := Named dtName (model :: Logic.Var nextDt
                                    :: nil) :: lhs |}
                                post (nextDt ++ "'")%string
                        end
                    end
                end
              else datatype_constructor_variable_already_in_scope x conName
            else wrong_number_of_constructor_arguments conName
        end
    end.
End stmtD.

End Make.
