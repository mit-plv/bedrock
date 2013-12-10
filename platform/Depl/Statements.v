(** Statements of the deeply embedded programming language *)

Require Import AutoSep.

Require Import Depl.Logic Depl.AlgebraicDatatypes.


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

(** Outcomes of symbolic execution *)
Inductive outcome :=
| Error
| Success (vs : vars)
| Returned (e : Logic.expr).

(** Symbolic execution of statements *)
Fixpoint stmtD (vs : vars) (s : stmt) : outcome :=
  match s with
    | Assign x e =>
      match exprD vs e with
        | None => Error
        | Some e' =>
          match vs x with
            | None => Error
            | Some _ => Success (vars_set vs x e')
          end
      end
    | Seq s1 s2 =>
      match stmtD vs s1 with
        | Success vs' => stmtD vs' s2
        | o => o
      end
    | Ret e =>
      match exprD vs e with
        | None => Error
        | Some e' => Returned e'
      end
  end.
