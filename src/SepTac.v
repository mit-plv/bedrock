Require Import IL SepIL.
Require Import Word Memory.
Import List.
Require Import DepList.

(** TODO: merge this into SepIL? *)

(** Non-dependent **)
Require Bedrock.ndep.Expr Bedrock.ndep.SepExpr.
Module SEP := SepExpr.SepExpr BedrockHeap ST.

Definition bedrock_types : list Expr.type :=
  (** TODO: I think that we want a comparable W **)
  {| Expr.Impl := W 
   ; Expr.Eq := fun x y => 
     match weq x y with
       | left pf => Some pf 
       | _ => None 
     end |} :: SEP.defaultType (settings * state)%type :: nil.

Lemma ApplyCancelSep : forall types funcs sfuncs (l r : SEP.sexpr (bedrock_types ++ types) (Expr.tvType O) (Expr.tvType 1)),
  (forall cs,
    match SEP.CancelSep nil l r with
      | {| SEP.vars := vars; 
           SEP.lhs := lhs; SEP.rhs_ex := rhs_ex; 
           SEP.rhs := rhs; SEP.SUBST := SUBST |} =>
           SEP.forallEach vars
             (fun VS : Expr.env (bedrock_types ++ types) =>
              SEP.exists_subst funcs VS
                (ExprUnify.env_of_Subst SUBST rhs_ex 0)
                (fun rhs_ex0 : Expr.env (bedrock_types ++ types) =>
                 SEP.himp funcs sfuncs nil rhs_ex0 VS cs lhs rhs))
    end) ->
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil l)
  ===>
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil r).
Proof.
  unfold Himp. intros. specialize (H specs). 
  apply SEP.ApplyCancelSep in H. unfold SEP.himp in *. assumption.
  simpl; tauto.
Qed.


Lemma Himp_to_SEP_himp : forall types funcs sfuncs 
  (l r : @SEP.sexpr (bedrock_types ++ types) (Expr.tvType 0) (Expr.tvType 1)),
  (forall cs, SEP.himp funcs sfuncs nil nil nil cs l r) ->
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil l)
  ===>
  (@SEP.sexprD _ funcs _ _ sfuncs nil nil r).
Proof.
  unfold Himp, SEP.himp. intuition.
Qed.

Ltac reflect_goal isConst Ts :=
  match goal with 
    | [ |- Himp ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
      let types := eval unfold bedrock_types in bedrock_types in
      let goals := constr:(L :: R :: nil) in
      let goals := eval unfold starB exB hvarB in goals in
      let v := SEP.reflect_sexprs pcT stateT ltac:(isConst) types tt tt goals in
      match v with
        | (?types, ?pcT, ?stT, ?funcs, ?sfuncs, ?L :: ?R :: nil) => 
          apply (@Himp_to_SEP_himp _ funcs sfuncs L R)
      end
  end.
