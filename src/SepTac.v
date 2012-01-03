Require Import IL SepIL.
Require Import Word.
Import List.
Require Import Env.

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
    match SEP.CancelSep cs nil l r with
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
  (@SEP.sexprD _ funcs _ _ sfuncs l nil nil)
  ===>
  (@SEP.sexprD _ funcs _ _ sfuncs r nil nil).
Proof.
  unfold Himp. intros. specialize (H specs). 
  apply SEP.ApplyCancelSep in H. unfold SEP.himp in *. assumption.
Qed.


Lemma Himp_to_SEP_himp : forall types funcs sfuncs 
  (l r : @SEP.sexpr (bedrock_types ++ types) (Expr.tvType 0) (Expr.tvType 1)),
  (forall cs, SEP.himp funcs sfuncs nil nil nil cs l r) ->
  (@SEP.sexprD _ funcs _ _ sfuncs l nil nil)
  ===>
  (@SEP.sexprD _ funcs _ _ sfuncs r nil nil).
Proof.
  unfold Himp, SEP.himp. intuition.
Qed.

Ltac reflect_goal isConst Ts :=
  match goal with 
    | [ |- Himp ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
      let Ts := eval unfold bedrock_types in bedrock_types in
      let goals := constr:(L :: R :: nil) in
      let goals := eval unfold starB exB hvarB in goals in
      let v := SEP.reflect_all pcT stateT ltac:(isConst) Ts goals in
      match v with
        | (?types, ?pcT, ?stT, ?funcs, ?sfuncs, ?L :: ?R :: nil) => 
          apply (@Himp_to_SEP_himp _ funcs sfuncs L R)
      end
  end.


(*
(** Dependent **)

Require Bedrock.dep.Expr Bedrock.dep.SepExpr.
Module SEP := SepExpr.SepExpr BedrockHeap ST.

Definition bedrock_types : list Expr.type :=
  (** TODO: I think that we want a comparable W **)
  {| Expr.Impl := W 
   ; Expr.Eq := fun x y => 
     match weq x y with
       | left pf => Some pf 
       | _ => None 
     end |} :: Expr.defaultType (settings * state)%type :: nil.

Lemma ApplyCancelSep : forall types funcs sfuncs l r,
  (forall cs,
    match SEP.CancelSep (funcs := funcs) (sfuncs := sfuncs) cs nil l r with
      | SEP.Prove vars u2 l' r' SUBST _ =>
        SEP.forallEach
        (fun VS : hlist (@Expr.tvarD (bedrock_types ++ types)) vars =>
          SEP.exists_subst VS SUBST
          (fun k : hlist (@Expr.tvarD (bedrock_types ++ types)) u2 => SEP.himp HNil k VS cs l' r'))
    end) ->
  (SEP.sexprD (pcType := Expr.tvTrans FO) (stateType := Expr.tvTrans (FS FO)) l HNil HNil)
  ===>
  (SEP.sexprD (pcType := Expr.tvTrans FO) (stateType := Expr.tvTrans (FS FO)) r HNil HNil).
Proof.
  unfold Himp. intros. specialize (H specs). 
  apply SEP.ApplyCancelSep in H. unfold SEP.himp in *. assumption.
Qed.


Lemma Himp_to_SEP_himp : forall types funcs sfuncs 
  (l r : @SEP.sexpr (bedrock_types ++ types) funcs (Expr.tvTrans FO) (Expr.tvTrans (FS FO)) sfuncs nil nil),
  (forall cs, 
    SEP.himp HNil HNil HNil cs l r) ->
  SEP.sexprD l HNil HNil ===> SEP.sexprD r HNil HNil.
Proof.
  unfold Himp, SEP.himp. intuition.
Qed.

Ltac reflect_goal isConst Ts :=
  match goal with 
    | [ |- Himp ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
      let Ts := eval unfold bedrock_types in bedrock_types in
      let goals := constr:(L :: R :: nil) in
      let goals := eval unfold starB exB hvarB in goals in
      let v := SEP.reflect_all pcT stateT ltac:(isConst) Ts goals in
      match v with
        | (?L, (?R, _)) => 
          idtac L ; idtac R ; 
          eapply (@Himp_to_SEP_himp _ _ _ L R)
      end
  end.
*)
