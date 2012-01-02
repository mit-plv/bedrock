Require Import Bedrock.ndep.Expr.
Require Import List.
Require Import EquivDec.
Require Import Bedrock.ndep.NatMap.
Require Import Env.

Set Implicit Arguments.
Set Strict Implicit.

Module SUBST := Bedrock.ndep.NatMap.IntMap.

Section Unify.
  Variable types : list type.

  Definition Subst := (*(dom : variables) := *)
    @SUBST.t (expr types).

  Definition empty_Subst : Subst :=
    SUBST.empty.

  Definition Subst_lookup (k : nat) (s : Subst) :=
    SUBST.find k s.

  Definition Subst_replace (k : nat) (v : expr types) (s : Subst) :=
  (** TODO: I need to make sure this doesn't do duplicates... **)
    SUBST.add k v s.
  
  Section Subst.
    Variable sub : Subst.

    Fixpoint env_of_Subst (ls : variables) (cur : nat)
      : list (tvar * option (expr types)) :=
      match ls with
        | nil => nil
        | a :: b => 
          (a, match Subst_lookup cur sub with
                | None => None 
                | Some e => Some e
              end) :: env_of_Subst b (S cur)
      end.
  End Subst.

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


  (** TODO: Right now this just does structural equality, it would be nice to
   ** generalize this to "provable equivalence", a simple form of this would handle 
   ** commutativity of plus for example
   ** - we can express this by modifying the correctness theorem to factor by equivalence
   **)

  (** TODO:
   ** This handles exitentials asymmetrically, i.e. it assumes that uL is nil.
   ** If uL is not nil, then this procedure is not even structurally complete
   **)

  Section fold_left2_opt.
    Variable T U : Type.
    Variable F : T -> T -> U -> option U.

    Fixpoint fold_left_2_opt (ls ls' : list T) (acc : U) : option U :=
      match ls, ls' with 
        | nil , nil => Some acc
        | x :: xs , y :: ys => 
          match F x y acc with
            | None => None
            | Some acc => fold_left_2_opt xs ys acc
          end
        | _ , _ => None
      end.
  End fold_left2_opt.


  Fixpoint exprUnify (l r : expr types) (ls rs : Subst) : option (Subst * Subst).
  refine (
    match l , r with
      | Const t v , Const t' v' =>
        match equiv_dec t t' with
          | left pf => match pf in _ = k return tvarD _ k -> _ with
                         | refl_equal => fun v' =>
                           if get_Eq t v v'
                           then Some (ls, rs)
                           else None
                       end v'
          | right _ => None
        end
      | Var v , Var v' =>
        if Peano_dec.eq_nat_dec v v' 
        then Some (ls, rs)
        else None
      | Func f args , Func f' args' => 
        match Peano_dec.eq_nat_dec f f' with
          | left pf =>
            fold_left_2_opt 
            (fun (l r : expr types) (acc : Subst * Subst) =>
              exprUnify l r (fst acc) (snd acc)) args args' (ls, rs)
          | right _ => None
        end
      | UVar u , _ => 
        match Subst_lookup u ls with
          | None => 
            Some (Subst_replace u r ls, rs)
          | Some r =>
            if seq_dec l r then Some (ls, rs) else None
        end
      | _ , UVar u =>
        match Subst_lookup u rs with
          | None => 
            Some (ls, Subst_replace u r rs)
          | Some r =>
            if seq_dec l r then Some (ls, rs) else None
        end
      | _ , _ => None
    end).
  Defined.

  (** I'd like to make these mutually recursive...**)
  Definition exprUnifyArgs (l r : list (expr types)) (ls rs : Subst)
    : option (Subst * Subst) :=
    fold_left_2_opt 
    (fun (l r : expr types) (acc : Subst * Subst) =>
      exprUnify l r (fst acc) (snd acc)) l r (ls, rs).

End Unify.