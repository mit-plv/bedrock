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

Definition test_seq l r : bool :=
  match l as l , r as r with
    | IL.Eq , IL.Eq => true
    | IL.Ne , IL.Ne => true
    | IL.Le , IL.Le => true
    | IL.Lt , IL.Lt => true
    | _ , _ => false
  end.

Theorem test_seq_compare : forall x y, test_seq x y = true -> x = y.
  destruct x; destruct y; simpl; (reflexivity || congruence).
Defined.

Definition reg_seq l r : bool := 
  match l as l , r as r with
    | IL.Sp , IL.Sp => true
    | IL.Rp , IL.Rp => true
    | IL.Rv , IL.Rv => true
    | _ , _ => false
  end.

Theorem reg_seq_compare : forall x y, reg_seq x y = true -> x = y.
  destruct x; destruct y; simpl; (reflexivity || congruence).
Defined.

Definition W_seq (l r : W) : bool :=
  match weq l r with
    | left pf => true
    | _ => false
  end.

Theorem W_seq_compare : forall x y, W_seq x y = true -> x = y.
  unfold W_seq; intros; destruct (weq x y); reflexivity || congruence.
Defined.

Lemma all_false_compare T : forall x y : T, false = true -> x = y.
  congruence.
Defined.

Definition bedrock_type_W : type := 
  {| Expr.Impl := W 
   ; Expr.Eqb := W_seq
   ; Expr.Eqb_correct := W_seq_compare
  |}. 
Definition bedrock_type_setting_X_state : type :=
  {| Expr.Impl := settings * state
   ; Expr.Eqb := fun _ _ => false
   ; Expr.Eqb_correct := @all_false_compare _
   |}.
Definition bedrock_type_setting : type :=
  {| Expr.Impl := state
   ; Expr.Eqb := fun _ _ => false
   ; Expr.Eqb_correct := @all_false_compare _
   |}. 
Definition bedrock_type_test : type :=
  {| Expr.Impl := IL.test
   ; Expr.Eqb := test_seq
   ; Expr.Eqb_correct := test_seq_compare
  |}.
Definition bedrock_type_reg : type :=
  {| Expr.Impl := IL.reg
     ; Expr.Eqb := reg_seq
     ; Expr.Eqb_correct := reg_seq_compare
  |}. 

Definition bedrock_types : list Expr.type :=
  bedrock_type_W ::
  bedrock_type_setting_X_state ::
  bedrock_type_setting ::
  bedrock_type_test ::
  bedrock_type_reg :: nil.

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
     ; Denotation := _ |} ::
    {| Domain := tvWord :: tvWord :: nil
     ; Range := tvProp
     ; Denotation := _ |} ::
     nil).
  refine (@wplus 32).
  refine (@wminus 32).
  refine (@wmult 32).
  refine comparator.
  refine Regs.
  refine (@wlt 32).
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
