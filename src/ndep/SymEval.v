Require Import List.
Require Import Heaps SepTheoryX.
Require Import IL.
Require Import Env.
Require Import Bedrock.ndep.Expr Bedrock.ndep.SepExpr Bedrock.ndep.Provers.

Require Import SepIL SepTac.

Set Implicit Arguments.
Set Strict Implicit.

(*
Module Evaluator (B : Heap with Definition mem := W -> B) (ST : SepTheoryX.SepTheoryXType B).
  
  Module Import SEP := SepExpr B ST.
*)
  Module Import SEP := SepTac.SEP.

  Section typed.

    Variable types' : list type.
    Definition pcType : tvar := tvType 0.
    Definition stateType : tvar := tvType 1.

    Definition types := bedrock_types ++ types'.

    Definition denotesTo (sfuncs : list (ssignature types pcType stateType)) (f : nat) 
      (Predicate : ssignature types pcType stateType) : Prop :=
      nth_error sfuncs f = Some Predicate.

    Record SymEval : Type :=
      { Predicate : ssignature types pcType stateType
      ; sym_read  : 
        forall (hyps args : list (expr types)) (p : expr types), option (expr types)
      ; sym_write : 
        forall (hyps : list (expr types)) (f : nat) (args : list (expr types)) (p v : expr types),
          option (sexpr types pcType stateType)
      ; sym_read_correct : forall funcs sfuncs f args uvars vars P cs
          hyps
          pe ve m s,
        denotesTo sfuncs f Predicate ->
        sym_read hyps args pe = Some ve ->
        hlist (FalseDefault funcs) hyps ->
        ST.satisfies 
          (@sexprD types funcs pcType stateType sfuncs (Star (Func f args) P) uvars vars)
          cs s m ->
        match exprD funcs uvars vars pe pcType , exprD funcs uvars vars ve pcType with
          | Some p , Some v =>
            ReadWord s m p = v 
          | _ , _ => False
        end
      ; sym_write_correct : forall funcs sfuncs f args uvars vars P cs
          hyps
          (pfW : tvarD types pcType = W)
          pe ve v m s s',
        denotesTo sfuncs f Predicate ->
        sym_write hyps f args pe ve = Some s' ->
        hlist (FalseDefault funcs) hyps ->
        exprD funcs uvars vars ve pcType = Some v ->
        ST.satisfies 
          (@sexprD types funcs pcType stateType sfuncs (Star (Func f args) P) uvars vars)
          cs s m ->
        match exprD funcs uvars vars pe pcType with
          | Some p =>
            ST.satisfies 
              (@sexprD types funcs pcType stateType sfuncs (Star s' P) uvars vars)
              cs s (WriteWord s m p v)
          | _ => False
        end
      }.
  End typed.
(*
End Evaluator.
*)



  Section ptsto32_sym_eval.
    Definition btypes : list type := bedrock_types.
    Variable types : list type.

    Definition ptsto32_Predicate : ssignature (btypes ++ types) pcType stateType :=
      Build_ssignature (btypes ++ types) pcType stateType (pcType :: pcType :: nil) (@ptsto32 nil).
      
  (** Let's see how this works with ptsto **)
    Definition ptsto32_sym_read (hyps args : list (expr (btypes ++ types))) (p : expr (btypes ++ types)) : option (expr (btypes ++ types)) :=
      match args with
        | p' :: v :: nil =>
          if seq_dec p p' then Some v else None
        | _ => None
      end.

    Definition ptsto32_sym_write (hyps : list (expr (btypes ++ types))) f (args : list (expr (btypes ++ types))) (p v : expr (btypes ++ types)) : option (sexpr (btypes ++ types) pcType stateType) :=
      match args with
        | p' :: v :: nil =>
          if seq_dec p p' then Some (Func f (p' :: v :: nil)) else None
        | _ => None
      end.

    Require Import PropXTac.

    Theorem ptsto32_sym_read_correct : forall (funcs : functions (Top.types types))
     (sfuncs : list (ssignature (Top.types types) pcType stateType))
     (f : nat) (args : list (expr (Top.types types)))
     (uvars vars0 : list {t : tvar & tvarD (Top.types types) t})
     (P : sexpr (Top.types types) pcType stateType)
     (cs : PropX.codeSpec (tvarD (Top.types types) pcType)
             (tvarD (Top.types types) stateType))
     (hyps : list (expr (Top.types types))) (pe ve : expr (Top.types types))
     (m : BedrockHeap.mem) (s : settings),
     denotesTo sfuncs f ptsto32_Predicate ->
     ptsto32_sym_read hyps args pe = Some ve ->
     hlist (FalseDefault funcs) hyps ->
     ST.satisfies (sexprD funcs sfuncs (Star (Func f args) P) uvars vars0) cs s
     m ->
     match exprD funcs uvars vars0 pe pcType , exprD funcs uvars vars0 ve pcType with
       | Some p , Some v => ReadWord s m p = v
       | _ , _ => False
     end.
    Proof.
      intros.
      destruct args; simpl in H0; try congruence.
      destruct args; simpl in H0; try congruence.
      destruct args; simpl in H0; try congruence.
      unfold denotesTo in *. simpl in *. rewrite H in H1; clear H. simpl in *. 
      repeat match goal with
        | [ H : (if ?X then Some _ else None) = Some _ |- _ ] =>
          destruct X; inversion H; clear H; subst
        | [ |- match ?X with
                 | Some _ => _
                 | None => False
               end ] => destruct X
      end;
      destruct H1 as [ ? [ ? ? ] ]; try solve [ propxFo ].
      propxFo. unfold implode in H8. subst.
      eapply satisfies_split in H1; eauto. destruct H1.
      repeat match goal with 
               | [ H : smem_get _ _ = _ |- _ ] =>
                 eapply satisfies_get in H; [ | eassumption ]; unfold BedrockHeap.mem_get in H; inversion H; subst
             end;
      eapply ReadWordFootprint; simpl; auto.
    Qed.

    Theorem ptsto32_sym_write_correct : forall (funcs : functions (Top.types types))
      (sfuncs : list (ssignature (Top.types types) pcType stateType))
      (f : nat) (args : list (expr (Top.types types)))
      (uvars vars0 : env (Top.types types))
      (P : sexpr (Top.types types) pcType stateType)
      (cs : PropX.codeSpec (tvarD (Top.types types) pcType)
        (tvarD (Top.types types) stateType))
      (hyps : list (expr (Top.types types))),
      tvarD (Top.types types) pcType = W ->
      forall (pe ve : expr (Top.types types))
        (v : tvarD (Top.types types) pcType) (m : BedrockHeap.mem)
        (s : settings) (s' : sexpr (Top.types types) pcType stateType),
        denotesTo sfuncs f ptsto32_Predicate ->
        ptsto32_sym_write hyps f args pe ve = Some s' ->
        hlist (FalseDefault funcs) hyps ->
        exprD funcs uvars vars0 ve pcType = Some v ->
        ST.satisfies (sexprD funcs sfuncs (Star (Func f args) P) uvars vars0) cs s
        m ->
        match exprD funcs uvars vars0 pe pcType with
          | Some p =>
            ST.satisfies (sexprD funcs sfuncs (Star s' P) uvars vars0) cs s
            (WriteWord s m p v)
          | None => False
        end.
    Proof.
      intros.
      destruct args; simpl in H1; try congruence.
      destruct args; simpl in H1; try congruence.
      destruct args; simpl in H1; try congruence.
      unfold denotesTo in *. simpl in *. rewrite H0 in H3; clear H0. simpl in *. 
      repeat match goal with
               | [ H : (if ?X then Some _ else None) = Some _ |- _ ] =>
                 destruct X; inversion H; clear H; subst
               | [ |- match ?X with
                        | Some _ => _
                        | None => False
                      end ] => destruct X
             end;
      destruct (exprD funcs uvars vars0 e0 pcType); destruct H3 as [ ? [ ? ? ] ]; propxFo.
    Admitted.

    Definition SymEval_ptsto32 : SymEval types :=
      {| Predicate := ptsto32_Predicate
       ; sym_read  := ptsto32_sym_read
       ; sym_write := ptsto32_sym_write
       ; sym_read_correct := ptsto32_sym_read_correct
       ; sym_write_correct := ptsto32_sym_write_correct
      |}.

  End  ptsto32_sym_eval.