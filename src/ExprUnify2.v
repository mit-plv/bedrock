Require Import Expr.
Require Import NatMap.
Require Import EquivDec.
Require Import List Bool.
Require Import GenRec.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO:
 ** this seems like a more difficult interface, but it seems realistic given 
 ** that you can't actually conclude more information after a substitution occurs
 ** you can only ensure that the substitution is consistent with the equation
 **)
Module Type Unifier.
  (** An environment that maintains a mapping from variables to their meaning **)
  Parameter Subst : list type -> Type.

  Section typed.
    Variable types : list type.
    
    Parameter Subst_empty : Subst types.

    (** The invariant that the substitution implies.
     **)
    Parameter SubstInv : forall (funcs : functions types) (meta_env var_env : env types), Subst types -> list (tvar * expr types * expr types) -> Prop.

    (** The actual unification algorithm **)
    Parameter exprUnify : nat -> expr types -> expr types -> Subst types -> option (Subst types).
    
    (** Substitute meta variables **)
    Parameter exprInstantiate : Subst types -> expr types -> expr types.

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

    Axiom SubstInv_empty : forall uenv env sub,
      SubstInv funcs uenv env sub nil.

    Axiom SubstInvD : forall uenv env sub ctx,
      SubstInv funcs uenv env sub ctx ->
      Forall (fun t_l_r => 
        let '(t,l,r) := t_l_r in
        unifies uenv env t l r) ctx.

    (** This is the soundness statement.
     ** TODO: Is this correct?
     **)
    Axiom exprUnify_sound : forall env uenv l r t sub sub' n ctx,
      exprUnify n l r sub = Some sub' ->
      SubstInv funcs uenv env sub ctx ->
      is_well_typed funcs uenv env l t = true ->
      is_well_typed funcs uenv env r t = true ->
      SubstInv funcs uenv env sub' ((t,l,r) :: ctx).

  End typed.

End Unifier.


Inductive R_expr (ts : list type) : expr ts -> expr ts -> Prop :=
| R_EqualL : forall t l r, R_expr l (Equal t l r)
| R_EqualR : forall t l r, R_expr r (Equal t l r)
| R_Not    : forall e, R_expr e (Not e)
| R_Func   : forall f args arg,
  In arg args -> R_expr arg (Func f args).
  
Lemma wf_R_expr' ts : well_founded (@R_expr ts).
Proof.  
  red; induction a; constructor; inversion 1; try assumption.

  subst. clear H0. generalize dependent y. generalize dependent l. clear.
  induction l; intros; simpl. inversion H3.
  inversion H3. inversion H. rewrite H0 in H4; assumption.
  inversion H; apply IHl; auto.
Defined.

Lemma wf_R_expr ts : well_founded (@R_expr ts).
Proof.
  let v := eval cbv beta iota zeta delta [ wf_R_expr' list_ind list_rec list_rect eq_ind eq_ind_r eq_rect eq_sym expr_ind ] in (@wf_R_expr' ts) in
  exact  v.
Defined.

Module SUBST := NatMap.IntMap.

Section typed.
  Variable types : list type.

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
        | Not e => Not (exprInstantiate e)
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
    SUBST.empty _.

  Fixpoint anyb T (F : T -> bool) (ls : list T) : bool :=
    match ls with
      | nil => false
      | l :: ls => F l || anyb F ls 
    end.

  Section Mentions.
    Variable uv : nat.

    Fixpoint mentionsU (e : expr types) : bool :=
      match e with
        | Const _ _ 
        | Var _ => false
        | UVar n => if equiv_dec uv n then true else false
        | Func _ args =>
          (fix anyb ls : bool := 
            match ls with
              | nil => false
              | l :: ls => mentionsU l || anyb ls
            end) args
        | Equal _ l r => mentionsU l || mentionsU r
        | Not e => mentionsU e
      end.
  End Mentions.

  Definition Subst_replace (k : nat) (v : expr types) (s : Subst) : option Subst :=
    let v' := exprInstantiate s v in
    if mentionsU k v' then
      None
    else
      let s := SUBST.add k v' s in
      let s := SUBST.map (exprInstantiate s) s in
      SUBST.fold (fun k e acc => 
        match acc with
          | None => None
          | _ => 
            if mentionsU k e then None else acc
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

  Section fold_in.
    Variable LS : list (expr types).
    Variable F : forall (l r : expr types), Subst -> In l LS -> option Subst.

    Fixpoint dep_in (ls rs : list (expr types)) (sub : Subst) : (forall l, In l ls -> In l LS) -> option Subst.
    refine (
      match ls as ls , rs as rs return (forall l, In l ls -> In l LS) -> option Subst with
        | nil , nil => fun _ => Some sub
        | l :: ls , r :: rs => fun pf_trans =>
          match F l r sub _ with
            | None => None
            | Some sub => dep_in ls rs sub (fun ls pf => pf_trans _ _)
          end
        | _ , _ => fun _ => None
      end).
    Focus 2.
    refine (or_intror _ pf).
    refine (pf_trans _ (or_introl _ (refl_equal _))).
    Defined.

    Variable F' : forall (l r : expr types), Subst -> option Subst.

    Fixpoint fold2_option (ls rs : list (expr types)) (sub : Subst) : option Subst :=
      match ls , rs with
        | nil , nil => Some sub
        | l :: ls , r :: rs =>
          match F' l r sub with
            | None => None
            | Some sub => fold2_option ls rs sub
          end
        | _ , _ => None
      end.

  End fold_in.

  Definition exprUnify_recursor bound_l 
    (recur : forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b bound_l -> expr types -> Subst -> option Subst)
    (r : expr types) (sub : Subst) : option Subst.
  refine (
        match bound_l as bound_l
          return (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b bound_l -> expr types -> Subst -> option Subst)
          -> option Subst
          with
          | (bound,l) =>
            match l as l , r as r 
              return (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound, l) -> expr types -> Subst -> option Subst)
              -> option Subst
              with
              | Const t v , Const t' v' => fun _ =>
                match equiv_dec t t' with
                  | left pf => match pf in _ = k return tvarD _ k -> _ with
                                 | refl_equal => fun v' =>
                                   if get_Eq t v v'
                                     then Some sub
                                     else None
                               end v'
                  | right _ => None
                end
              | Var v , Var v' => fun _ => 
                if Peano_dec.eq_nat_dec v v' 
                  then Some sub
                  else None
              | Func f1 args1 , Func f2 args2 => fun recur =>
                match equiv_dec f1 f2 with
                  | left _ => 
                    @dep_in args1 (fun l r s pf => recur (bound, l) _ r s) args1 args2 sub (fun _ pf => pf)
                  | right _ => None
                end
              | Equal t1 e1 f1 , Equal t2 e2 f2 => fun recur =>
                if equiv_dec t1 t2 then
                  match recur (bound, e1) _ e2 sub with
                    | None => None
                    | Some sub => recur (bound, f1) _ f2 sub
                  end
                  else
                    None
              | Not e1 , Not e2 => fun recur =>
                recur (bound,e1) _ e2 sub
              | UVar u , _ =>
                match Subst_lookup u sub with
                  | None => fun recur =>
                    Subst_replace u r sub
                  | Some l' =>
                    match bound as bound return 
                      (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound,UVar u) -> expr types -> Subst -> option Subst)
                      -> option Subst with
                      | 0 => fun _ => None
                      | S bound => fun recur => recur (bound, l') _ r sub
                    end
                end
              | l , UVar u =>
                match Subst_lookup u sub with
                  | None => fun recur =>
                    Subst_replace u l sub
                  | Some r' =>
                    match bound as bound return 
                      (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound,l) -> expr types -> Subst -> option Subst)
                      -> option Subst with
                      | 0 => fun _ => None
                      | S bound => fun recur => recur (bound, l) _ r' sub
                    end
                end
              | _ , _ => fun _ => None
            end 
        end recur
      ); try solve [ apply GenRec.L ; constructor | apply GenRec.R ; constructor; assumption ].
  Defined.

  (** index by a bound, since the termination argument is not trivial
   ** it is guaranteed to not make more recursions than the number of
   ** uvars.
   **)
  Definition exprUnify (bound : nat) (l : expr types) : expr types -> Subst -> option Subst :=
    (@Fix _ _ (guard 4 (GenRec.wf_R_pair GenRec.wf_R_nat (@wf_R_expr types)))
      (fun _ => expr types -> Subst -> option Subst) exprUnify_recursor) (bound,l).

  Section equiv.
    Variable A : Type.
    Variable R : A -> A -> Prop.
    Hypothesis Rwf : well_founded R.
    Variable P : A -> Type.
    
    Variable equ : forall x, P x -> P x -> Prop.
    Hypothesis equ_Equiv : forall x, RelationClasses.Equivalence (@equ x).

    Variable F : forall x : A, (forall y : A, R y x -> P y) -> P x.

    Lemma Fix_F_equ : forall (x : A) (r : Acc R x),
      equ (@F x (fun (y : A) (p : R y x) => Fix_F P F (Acc_inv r p)))
          (Fix_F P F r).
    Proof.
      eapply Acc_inv_dep; intros.
      simpl in *. reflexivity.
    Qed.

    Lemma Fix_F_inv_equ : 
       (forall (x : A) (f g : forall y : A, R y x -> P y),
        (forall (y : A) (p : R y x), equ (@f y p) (g y p)) -> equ (@F x f) (@F x g)) ->
       forall (x : A) (r s : Acc R x), equ (Fix_F P F r) (Fix_F P F s).
    Proof.
      intro. intro. induction (Rwf x). intros.
      erewrite <- Fix_F_equ. symmetry. erewrite <- Fix_F_equ. symmetry.
      eapply H. intros. eauto.
    Qed.

  End equiv.

  Lemma Equiv_equiv : Equivalence
    (fun f g : expr types -> Subst -> option Subst =>
      forall (a : expr types) (b : Subst), f a b = g a b).
  Proof.
    constructor; eauto.
    red. intros. rewrite H; eauto.
  Qed.



  Lemma exprUnify_recursor_inv : forall (bound : nat)
    e1 e2 (sub : Subst) (A B : Acc _ (bound,e1))
    (w : well_founded (R_pair R_nat (R_expr (ts:=types)))),
    Fix_F (fun _ : nat * expr types => expr types -> Subst -> option Subst)
    exprUnify_recursor A e2 sub =
    Fix_F (fun _ : nat * expr types => expr types -> Subst -> option Subst)
    exprUnify_recursor B e2 sub.
  Proof.
    intros.
    eapply (@Fix_F_inv_equ (nat * expr types) (R_pair R_nat (R_expr (ts:=types)))
      w
      (fun _ : nat * expr types => expr types -> Subst -> option Subst)
      (fun x f g => forall a b, f a b = g a b)
      (fun _ => Equiv_equiv)
      exprUnify_recursor).
    clear. intros.
      unfold exprUnify_recursor. destruct x. destruct e; destruct a; auto;
      repeat match goal with 
               | _ => reflexivity
               | [ H : _ |- _ ] => rewrite H
               | [ |- context [ match ?X with 
                                  | _ => _
                                end ] ] => destruct X
             end.
      generalize (fun (l1 : expr types) (pf : In l1 l) => pf).
      assert (
        forall l' l0 b, forall i : forall l1 : expr types, In l1 l' -> In l1 l,
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            f (n, l1)
            (R R_nat (R_expr (ts:=types)) n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i =
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            g (n, l1)
            (R R_nat (R_expr (ts:=types)) n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i).
      induction l'; simpl in *; intros; auto.
      destruct l1; auto. 
      rewrite H. destruct (g (n, a)); auto.
      eapply H0.
  Qed.


  Theorem exprUnify_unroll : forall bound l r sub,
    exprUnify bound l r sub = 
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
      | Func f1 args1 , Func f2 args2 =>
        match equiv_dec f1 f2 with
          | left _ =>
            fold2_option (@exprUnify bound) args1 args2 sub
          | right _ => None
        end
      | Equal t1 e1 f1 , Equal t2 e2 f2 =>
        if equiv_dec t1 t2 then
          match exprUnify bound e1 e2 sub with
            | None => None
            | Some sub => exprUnify bound f1 f2 sub
          end
        else
          None
      | Not e1, Not e2 =>
        exprUnify bound e1 e2 sub
      | UVar u , _ =>
        match Subst_lookup u sub with
          | None => Subst_replace u r sub
          | Some l' =>
            match bound with
              | 0 => None
              | S bound => exprUnify bound l' r sub
            end
        end
      | l , UVar u =>
        match Subst_lookup u sub with
          | None => Subst_replace u l sub
          | Some r' =>
            match bound with
              | 0 => None
              | S bound => exprUnify bound l r' sub
            end
        end
      | _ , _ => None
    end.
  Proof.
    intros. unfold exprUnify at 1.
    match goal with
      | [ |- context [ guard ?X ?Y ] ] =>
        generalize (guard X Y)
    end.
    intros.    


    unfold Fix.
    rewrite <- (@Fix_F_equ (nat * expr types) (R_pair R_nat (R_expr (ts:=types)))
      (fun _ : nat * expr types => expr types -> Subst -> option Subst)
      (fun x f g => forall a b, f a b = g a b)
      (fun _ => Equiv_equiv)
      exprUnify_recursor
      (bound,l)
      (w (bound,l))
      r sub).
    destruct l; destruct r; simpl; intros; auto;
      try solve [
        repeat match goal with
                 | [ |- context [ match ?X with 
                                    | _ => _ 
                                  end ] ] => destruct X
               end; try solve [ auto | 
                 unfold exprUnify, Fix ;
                   eapply exprUnify_recursor_inv; eauto ] ].
    Focus 2.
    destruct (equiv_dec t t0); auto.
    unfold exprUnify, Fix.
    erewrite exprUnify_recursor_inv; eauto.
    instantiate (1 := (guard 4 (wf_R_pair wf_R_nat (wf_R_expr (ts:=types))) (bound, l1))).
    match goal with 
      | [ |- match ?X with 
               | _ => _ 
             end = _ ] => destruct X
    end; auto.
    erewrite exprUnify_recursor_inv; eauto.

    match goal with
      | [ |- match ?X with
               | _ => _
             end = _ ] => destruct X; auto
    end.
    generalize (fun (l1 : expr types) (pf : In l1 l) => pf).
    assert (forall l' l0 sub,
      forall i : (forall l1 : expr types, In l1 l' -> In l1 l),
      dep_in l
      (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
        @Fix_F _ _ (fun _ : nat * expr types => expr types -> Subst -> option Subst)
        exprUnify_recursor (bound, l1) (@Acc_inv (nat * expr types)
           (@R_pair nat (expr types) R_nat (@R_expr types))
           (bound, @Func types f l) (w (bound, @Func types f l)) 
           (bound, l1)
           (@R nat (expr types) R_nat (@R_expr types) bound l1
              (@Func types f l) (@R_Func types f l l1 pf))) r0 s) l' l0 sub i =
      fold2_option (exprUnify bound) l' l0 sub).
    induction l'; simpl; intros; destruct l1; auto.
    erewrite exprUnify_recursor_inv; eauto.
    instantiate (1 := (guard 4 (wf_R_pair wf_R_nat (wf_R_expr (ts:=types))) (bound, a))).
    unfold exprUnify, Fix.
    match goal with
      | [ |- match ?X with
               | _ => _
             end = _ ] => destruct X; auto
    end.
    eapply H.
  Qed.

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

    Theorem exprUnify_correct : forall env uvars l r t sub sub' n,
      exprUnify n l r sub = Some sub' ->
      existsEach uvars (fun uenv =>
        Subst_equations funcs env sub uenv 0 uenv /\  
        is_well_typed funcs uenv env l t = true /\ 
        is_well_typed funcs uenv env r t = true) ->
      existsEach uvars (fun uenv =>
        Subst_equations funcs env sub' uenv 0 uenv /\  
        unifies funcs uenv env t l r).
    Proof.
(*
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
*)
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
