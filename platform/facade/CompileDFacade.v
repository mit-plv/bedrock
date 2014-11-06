Set Implicit Arguments.

Require Import FacadeFacts.
Require Import DFacadeFacts.
Require Import Facade.
Require Import DFacade.

Require Import Facade.NameDecoration.
Require Import SyntaxExpr.
Require Import String.
Local Open Scope string_scope.

Local Notation PRE := tmp_prefix.
Definition fun_ptr_varname := PRE ++ "fptr".

Fixpoint compile (s : Stmt) : Facade.Stmt :=
  match s with
    | Skip => Facade.Skip
    | Seq a b => Facade.Seq (compile a) (compile b)
    | If e t f => Facade.If e (compile t) (compile f)
    | While e c => Facade.While e (compile c)
    | Assign x e => Facade.Assign x e
    | Call x f args => 
      Facade.Seq 
        (Facade.Label fun_ptr_varname f)
        (Facade.Call x (Var fun_ptr_varname) args)
  end.

(*here*)

Section ADTValue.

  Variable ADTValue : Type.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).

  Require Import Memory.
  Require Import GLabel.

  Notation FEnv := (@Facade.Env ADTValue).

  Definition specs_fs_agree (env : Env) (env : Env) :=
    let labels := fst env in
    let fs := snd env in
    forall p spec, 
      fs p = Some spec <-> 
      exists (lbl : glabel),
        labels lbl = Some p /\
        find lbl specs = Some spec.

  Definition labels_in_scope (specs : Specs) (labels : glabel -> option W) :=
    forall lbl, In lbl specs -> labels lbl <> None.

  Definition specs_stn_injective (specs : Specs) stn := forall lbl1 lbl2 (w : W), In lbl1 specs -> In lbl2 specs -> stn lbl1 = Some w -> stn lbl2 = Some w -> lbl1 = lbl2.

  Definition specs_env_agree (specs : Specs) (env : Env) :=
    labels_in_scope specs (fst env) /\
    specs_stn_injective specs (fst env) /\
    specs_fs_agree specs env.



