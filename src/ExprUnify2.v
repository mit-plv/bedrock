Require Import Expr.
Require Import NatMap.
Require Import EquivDec.
Require Import List Bool.

Set Implicit Arguments.
Set Strict Implicit.

Module SUBST := NatMap.IntMap.

Section typed.
  Variable types : list type.

  Fixpoint uvars_of (e : expr types) : list nat :=
    match e with
      | Const _ _ 
      | Var _ => nil
      | UVar n => n :: nil
      | Func _ args => fold_right (fun x a => a ++ uvars_of x) nil args
      | Equal _ l r => uvars_of l ++ uvars_of r
    end.
  
  Definition Subst : Type :=
    SUBST.t (expr types).

  Definition Subst_lookup (k : nat) (s : Subst) : option (expr types) :=
    SUBST.find k s.

  Section Instantiate.
    Variable sub : Subst.

    Fixpoint exprInstantiate (e : expr types) : expr types :=
      match e with 
        | Const _ _ 
        | Var _ => e
        | UVar n => match Subst_lookup n sub with
                      | None => e 
                      | Some v => v
                    end
        | Func f args => Func f (map exprInstantiate args)
        | Equal t l r => Equal t (exprInstantiate l) (exprInstantiate r)
      end.
  End Instantiate.

  Section SubstDenote.
    Variable funcs : functions types.
    Variable vars : env types.
    Variable sub : Subst.

    Fixpoint Subst_equations (ls : env types) (cur : nat) : env types -> Prop :=
      match ls with
        | nil => fun _ => True
        | l :: ls =>
          let P := Subst_equations ls (S cur) in
          match Subst_lookup cur sub with
            | None => P
            | Some v => fun g => 
              match exprD funcs g vars v (projT1 l) with 
                | Some v => v = projT2 l
                | None => False
              end /\ P g
          end
      end.
  End SubstDenote.

  Definition empty_Subst : Subst :=
    SUBST.empty.

  Fixpoint allb T (F : T -> bool) (ls : list T) : bool :=
    match ls with
      | nil => true
      | l :: ls => F l && allb F ls
    end.

  Definition consistentb (k : nat) (e : expr types) : bool :=
    if In_dec equiv_dec k (uvars_of e) then false else true.

  Definition Subst_replace (k : nat) (v : expr types) (s : Subst) : option Subst :=
    let v' := exprInstantiate s v in
    if In_dec equiv_dec k (uvars_of v') then
      None
    else
      let s := SUBST.add k v' s in
      let s := SUBST.map (fun _ => exprInstantiate s) s in
      SUBST.fold (fun k e acc => match acc with
                                   | None => None
                                   | Some acc => 
                                     let e := exprInstantiate s e in
                                     if consistentb k e then
                                       Some (SUBST.add k e acc)
                                     else None
                                 end) s (Some s).

  Definition get_Eq (t : tvar) : forall x y : tvarD types t, option (x = y) :=
    match t as t return forall x y : tvarD types t, option (x = y) with
      | tvProp => fun _ _ => None
      | tvType t => 
        match nth_error types t as k 
          return forall x y : match k with
                                | Some t => Impl t
                                | None => Empty_set
                              end, option (x = y)
          with
          | None =>
            fun x _ => 
              match x with
              end
          | Some t => Expr.Eq t
        end 
    end.

  (** index by a bound, since the termination argument is not trivial
   ** it is guaranteed to not make more recursions than the number of
   ** uvars.
   **)
  Fixpoint exprUnify (l r : expr types) (sub : Subst) : option Subst.
  refine (
    match l , r with
      | Const t v , Const t' v' =>
        match equiv_dec t t' with
          | left pf => match pf in _ = k return tvarD _ k -> _ with
                         | refl_equal => fun v' =>
                           if get_Eq t v v'
                           then Some sub
                           else None
                       end v'
          | right _ => None
        end
      | Var v , Var v' =>
        if Peano_dec.eq_nat_dec v v' 
        then Some sub
        else None
      | Func f args , Func f' args' => None
(*
        match Peano_dec.eq_nat_dec f f' with
          | left pf => None
            fold_left_2_opt 
            (fun (l r : expr types) (acc : Subst * Subst) =>
              exprUnify l r (fst acc) (snd acc)) args args' (ls, rs)
          | right _ => None
        end
*)
      | Equal t1 e1 f1 , Equal t2 e2 f2 =>
        if equiv_dec t1 t2 then
          match exprUnify e1 e2 sub with
            | None => None
            | Some sub => exprUnify f1 f2 sub
          end
        else
          None
      | UVar u , _ => None
(*
        match Subst_lookup u sub with
          | None => 
            Some (Subst_replace u r ls, rs)
          | Some r =>
            if seq_dec l r then Some (ls, rs) else None
        end
*)
      | _ , UVar u => None 
(*
        match Subst_lookup u rs with
          | None => 
            Some (ls, Subst_replace u l rs)
          | Some r =>
            if seq_dec l r then Some (ls, rs) else None
        end
*)
      | _ , _ => None
    end).
  Defined.

  (** Syntactic Unification **)
  Section Unifies.
    Variable funcs : functions types.
    Variable vars : env types.
    
    (** NOTE: the meaning of Prop isn't quite perfect. We currently reflect Props
     ** but we actually mean proofs, i.e. using the Provable predicate.
     **)
    Definition unifies uenv env (t : tvar) (l r : expr types) : Prop :=
      match exprD funcs uenv env l t , exprD funcs uenv env r t with
        | Some l , Some r => match t as t return tvarD types t -> tvarD types t -> Prop with
                               | tvProp => fun l r => l <-> r (** we'll weaken things a bit more **)
                               | tvType _ => fun l r => l = r
                             end l r
        | _ , _ => False
      end.
  End Unifies.


  Section Correctness.
    Variable funcs : functions types.
    Variable vars : env types.

    Theorem exprUnify_correct : forall env uvars l r t sub sub',
      exprUnify l r sub = Some sub' ->
      existsEach uvars (fun uenv =>
        Subst_equations funcs env sub uenv 0 uenv /\  
        is_well_typed funcs uenv env l t = true /\ 
        is_well_typed funcs uenv env r t = true) ->
      existsEach uvars (fun uenv =>
        Subst_equations funcs env sub' uenv 0 uenv /\  
        unifies funcs uenv env t l r).
    Proof.
      induction l; destruct r; intuition; simpl in *; try congruence;
        repeat (match goal with 
                  | [ H : existsEach _ _ |- _ ] => 
                    apply existsEach_sem in H
                  | [ H : exists x, _ |- _ ] => destruct H
                  | [ H : match ?X with 
                            | left _ => _
                            | right _ => _ 
                          end = _ |- _ ] => destruct X; try congruence
                  | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                  | [ H : match ?X with 
                            | None => _
                            | Some _ => _ 
                          end = _ |- _ ] => revert H; case_eq X; intros; try congruence
                end; intuition; unfold equiv in *; subst); 
        eapply existsEach_sem.
      Focus. (** const **)
        exists x; intuition. unfold unifies; simpl. repeat rewrite EquivDec_refl_left.
        destruct t3; intuition auto.
      
      Focus. (** var **)
        exists x1; intuition eauto.
        unfold unifies; simpl. rewrite H. destruct t; intuition eauto.

      Focus. (** equal **)
        destruct t1; try congruence.
        apply andb_true_iff in H4. apply andb_true_iff in H2.
        intuition.
        eapply IHl1 with (t := t0) in H; [ | apply existsEach_sem; exists x; intuition ].
        apply existsEach_sem in H. destruct H; intuition.
        eapply IHl2 with (t := t0) in H1; [ | apply existsEach_sem; exists x0; intuition ].

        Focus.
        apply existsEach_sem in H1. destruct H1; intuition.
        exists x1; intuition eauto. unfold unifies; simpl.
    Admitted.
  End Correctness.

End typed.

Module TEST.
  Definition types := ({| Impl := nat ; Eq := fun _ _ => None |} :: nil).
  
  Definition vars_env : env types := nil.
  Definition uvars := tvType 0 :: tvType 0 :: tvType 0 :: nil.
  Definition subst := 
    let s := empty_Subst types in
    Subst_replace 1 (UVar 0) s.
  Definition funcs : functions types := nil.

  Goal 
    existsEach uvars (fun uenv =>
      match subst with 
        | None => False
        | Some subst => 
          Subst_equations funcs vars_env subst uenv 0 uenv 
      end /\  
      AllProvable funcs uenv vars_env 
        ((Equal (tvType 0) (UVar 0) (UVar 2)) :: 
         (Equal (tvType 0) (UVar 0) (@Const types (tvType 0) 3)) :: nil)).
    compute.
  Abort.
End TEST.