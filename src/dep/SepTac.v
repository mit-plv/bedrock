Require Import IL SepIL.
Require Import Word.
Import List.
Require Import DepList.


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
