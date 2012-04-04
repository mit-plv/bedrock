Require Import Expr.
Require Import NatMap.
Require Import EquivDec.
Require Import List.

Module SUBST := NatMap.IntMap.

Section typed.
  Variable types : list type.

  Definition Subst :=
    @SUBST.t (expr types).

  Definition empty_Subst : Subst :=
    SUBST.empty.

  Definition Subst_lookup (k : nat) (s : Subst) :=
    SUBST.find k s.

  Definition Subst_replace (k : nat) (v : expr types) (s : Subst) :=
    SUBST.add k v s.

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

  Check Expr.forallEach.



  Variable funcs : functions types.

  Fixpoint Subst_existsEach (ls : variables) (sub : Subst) (cur : nat)
    (P : env types -> (env types -> Prop) -> Prop) : Prop :=
    match ls with
      | nil => P nil (fun _ => True)
      | l :: ls =>
        exists x : tvarD types l, 
          Subst_existsEach ls sub (S cur) (fun g p => 
            let env' := @existT _ (tvarD types) _ x :: g in
            match Subst_lookup cur sub with
              | None => P env' p
              | Some v => P env' (fun env => 
                exprD funcs env nil v l = Some x /\ p env)
            end)
    end.

  Theorem exprUnify_correct : forall env uvars l r t sub sub',
    exprUnify l r sub = Some sub' ->
    Subst_existsEach uvars sub' 0 (fun uenv eqs => 
      match exprD funcs uenv env l t , exprD funcs uenv env r t with
        | Some l , Some r => l = r
        | _ , _ => False
      end /\ eqs uenv) ->
    Subst_existsEach uvars sub 0 (fun uenv eqs => 
      match exprD funcs uenv env l t , exprD funcs uenv env r t with
        | Some l , Some r => l = r
        | _ , _ => False
      end /\ eqs uenv).
  Proof.
    induction l; destruct r; simpl; intros; try congruence.
    Focus. (** Const **)
      destruct (equiv_dec t t1); try congruence.
      generalize dependent t2.
      generalize e. rewrite <- e. admit. (** this case is problematic **)

    Focus. (** Var **)
    destruct (Peano_dec.eq_nat_dec x x0); try congruence.
    inversion H; clear H; subst; eauto.

    Focus. (** Equal **)
    destruct (equiv_dec t t0); try congruence.
    revert H2; case_eq (exprUnify l1 r1 sub); intros; try congruence.
    eapply IHl1 with (t := t) in H.
    eapply IHl2 with (t := t) in H2.
  Admitted.


End typed.

Module TEST.
  Definition types := ({| Impl := nat ; Eq := fun _ _ => None |} :: nil).
  
  Definition vars_env : env types := nil.
  Definition uvars := tvType 0 :: tvType 0 :: tvType 0 :: nil.
  Definition subst := 
    let s := empty_Subst types in
    Subst_replace types 1 (UVar 0) s.
  Definition funcs : functions types := nil.

  Print Provable.

  Goal 
    Subst_existsEach types funcs uvars subst 0 (fun env other =>
      Provable funcs env vars_env (Equal (tvType 0) (UVar 0) (UVar 2)) /\ other env).
    compute.
    do 3 eexists.
  Abort.
End TEST.