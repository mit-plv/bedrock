(** This file contains generic environment information for the Bedrock IL
 **)
Require Import List.
Require Import Word.
Require Import Expr.
Require Import Env.
Require Import Memory IL.
Require Import TypedPackage.

Set Implicit Arguments.
Set Strict Implicit.

Definition test_seq l r : option (l = r) :=
  match l as l , r as r with
    | IL.Eq , IL.Eq => Some (refl_equal _)
    | IL.Ne , IL.Ne => Some (refl_equal _)
    | IL.Le , IL.Le => Some (refl_equal _)
    | IL.Lt , IL.Lt => Some (refl_equal _)
    | _ , _ => None
  end.

Definition reg_seq l r : option (l = r) :=
  match l as l , r as r with
    | IL.Sp , IL.Sp => Some (refl_equal _)
    | IL.Rp , IL.Rp => Some (refl_equal _)
    | IL.Rv , IL.Rv => Some (refl_equal _)
    | _ , _ => None
  end.

Definition W_seq (l r : W) : option (l = r) :=
  match weq l r with
    | left pf => Some pf 
    | _ => None 
  end.

Definition bedrock_types : list Expr.type :=
  {| Expr.Impl := W 
   ; Expr.Eq := W_seq
   |} ::
  {| Expr.Impl := settings * state
   ; Expr.Eq := fun _ _ => None
   |} ::
  {| Expr.Impl := state
   ; Expr.Eq := fun _ _ => None
   |} ::
  {| Expr.Impl := IL.test
   ; Expr.Eq := test_seq
   |} ::
  {| Expr.Impl := IL.reg
   ; Expr.Eq := reg_seq
   |} :: nil.

Definition bedrock_types_r : Repr Expr.type :=
  Eval cbv beta iota zeta delta [ listToRepr bedrock_types ]
    in (listToRepr bedrock_types Expr.EmptySet_type).

Definition comparator (t : IL.test) (l r : W) : Prop :=
  match t with
    | IL.Eq => l = r
    | IL.Ne => l = r -> False
    | IL.Lt => wlt l r
    | IL.Le => not (wlt r l)
  end.

Section typed_ext.
  Variable types' : list type.
  Local Notation "'TYPES'" := (repr bedrock_types_r types').

  Local Notation "'pcT'" := (tvType 0).
  Local Notation "'tvWord'" := (tvType 0).
  Local Notation "'stT'" := (tvType 1).
  Local Notation "'tvState'" := (tvType 2).
  Local Notation "'tvTest'" := (tvType 3).
  Local Notation "'tvReg'" := (tvType 4).

  Definition bedrock_funcs : functions (repr bedrock_types_r types').
  refine (
    {| Domain := tvWord :: tvWord :: nil
     ; Range := tvWord
     ; Denotation := _ |} ::
    {| Domain := tvWord :: tvWord :: nil
     ; Range := tvWord
     ; Denotation := _ |} ::
    {| Domain := tvWord :: tvWord :: nil
     ; Range := tvWord
     ; Denotation := _ |} ::
    {| Domain := tvTest :: tvWord :: tvWord :: nil
     ; Range := tvProp
     ; Denotation := _ |} :: 
    {| Domain := tvState :: tvReg :: nil
     ; Range := tvWord
     ; Denotation := _ |} :: nil).
  refine (@wplus 32).
  refine (@wminus 32).
  refine (@wmult 32).
  refine comparator.
  refine Regs.
  Defined.

  Definition bedrock_funcs_r : Repr (signature (repr bedrock_types_r types')) :=
    Eval cbv beta iota zeta delta [ listToRepr bedrock_funcs ]
      in (listToRepr bedrock_funcs (Default_signature _)).
  
  Variable funcs' : functions TYPES.
  Definition funcs := repr bedrock_funcs_r funcs'.
  
  Definition fPlus (l r : expr TYPES) : expr TYPES :=
    Expr.Func 0 (l :: r :: nil).
  Definition fMinus (l r : expr TYPES) : expr TYPES :=
    Expr.Func 1 (l :: r :: nil).
  Definition fMult (l r : expr TYPES) : expr TYPES :=
    Expr.Func 2 (l :: r :: nil).

  Theorem fPlus_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l (tvType 0) , exprD funcs uvars vars r (tvType 0) with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fPlus l r) (tvType 0) = Some (wplus lv rv)
      | _ , _ => True
    end.
  Proof.
    intros; simpl; unfold eq_ind_r; simpl;
      repeat match goal with
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end ] => destruct X
             end; auto.
  Qed.
  Theorem fMinus_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fMinus l r) tvWord = Some (wminus lv rv)
      | _ , _ => True
    end.
  Proof.
    intros; simpl; unfold eq_ind_r; simpl;
      repeat match goal with
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end ] => destruct X
             end; auto.
  Qed.
  Theorem fMult_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fMult l r) tvWord = Some (wmult lv rv)
      | _ , _ => True
    end.
  Proof.
    intros; simpl; unfold eq_ind_r; simpl;
      repeat match goal with
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end ] => destruct X
             end; auto.
  Qed.
End typed_ext.


Module BedrockCoreEnv <: CoreEnv.
  Definition core := 
    Eval unfold bedrock_types_r in bedrock_types_r.
  
  Definition pc := tvType 0.
  Definition st := tvType 1.
End BedrockCoreEnv.

Require SepIL.
