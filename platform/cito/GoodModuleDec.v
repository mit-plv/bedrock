Set Implicit Arguments.

Section TopSection.

  Require Import IsGoodModule.

  Notation MName := SyntaxModule.Name.
  Notation FName := SyntaxFunc.Name.
  Notation Funcs := SyntaxModule.Functions.

  Require Import GoodModule.

  Open Scope bool_scope.
  Notation "! b" := (negb b) (at level 35).

  Definition GoodModuleName_bool s := ! (prefix "_" s).

  Require Import List.

  Fixpoint NoDup_bool A (eqb : A -> A -> bool) (ls : list A) {struct ls} :=
    match ls with
      | nil => false
      | x :: xs => forallb (fun e => ! (eqb e x)) xs && NoDup_bool eqb xs
    end.

  Require Import SyntaxModule.

  Definition GoodFunction_bool (f : Func) := 
    let body := Body f in 
    let local_vars := get_local_vars body (ArgVars f) (RetVar f) in
    let all_vars := ArgVars f ++ local_vars in
    NoDup_bool string_eq (ArgVars f) &&
    NoUninitialized_bool f &&
    syn_req_bool all_vars (depth body) body 

  Definition GoodFunctions_bool fs := forallb GoodFunction_bool fs.

  Definition GoodModule_bool (m : Module) :=
    GoodModuleName_bool (MName m) &&
    GoodFunctions_bool (Funcs m) &&
    NoDup_bool string_eq (List.map FName (Funcs m)).