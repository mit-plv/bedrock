Require Import Bedrock.ndep.Expr.
Require Import List.
Require Import EquivDec.
Require Import Bedrock.ndep.NatMap.

Set Implicit Arguments.
Set Strict Implicit.

Module SUBST := Bedrock.ndep.NatMap.IntMap.

Section Unify.
  Variable types : list type.

  Definition Subst (dom : variables) := 
    SUBST.t (expr types).

  Section Subst.
    Variables dom : variables.
    
    Definition empty_Subst : Subst dom :=
      SUBST.empty _.

    Definition Subst_lookup (k : nat) (s : Subst dom) :=
      SUBST.find k s.

    Definition Subst_replace (k : nat) (v : expr types) (s : Subst dom) :=
      (** TODO: I need to make sure this doesn't do duplicates... **)
      SUBST.add k v s.

    Variable sub : Subst dom.

    Fixpoint env_of_Subst (ls : variables) (cur : nat)
      : list (option (expr types)) :=
      match ls with
        | nil => nil
        | a :: b => 
          match Subst_lookup cur sub with
            | None => None 
            | Some e => Some e
          end :: env_of_Subst b (S cur)
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
          | Some t => Eq t 
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

  Fixpoint exprUnify dom (r l : expr types) (s : Subst dom) : option (Subst dom).
(*
  refine (
    match r with
      | Const t v =>
        match l in expr _ _ _ T 
          return tvarD T -> Subst uR uL vs -> option (Subst uR uL vs) with
          | Const t' v' => fun v s =>
            if get_Eq t' v v'
            then Some s
            else None
          | _ => fun _ _ => None
        end v
      | Var v => fun l s =>
        match l with
          | Var v' => if finEq v v' then Some s else None
          | _ => None
        end
      | UVar u => fun l s =>
        match Subst_lookup u s with
          | None => 
            Some (Subst_replace u l s)
          | Some r =>
            if seq_dec l r then Some s else None
        end
      | Func f args => fun l s =>
        match l in expr _ _ _ T 
          return _
          with
          | Func f' args' =>
            match finEq f f' with
              | left pf =>
                match pf in _ = F 
                  return hlist (expr funcs uL vs) (Domain (get funcs F)) -> option _ 
                  with
                  | refl_equal => fun args' => 
                    let combine acc t (r : expr funcs uR vs t) (l : expr funcs uL vs t) :=
                      match acc with
                        | None => None
                        | Some s => 
                          exprUnify r l s 
                      end 
                    in
                    hlist_fold2 combine args args' (Some s)
                end args'
              | right _ => None
            end
          | _ => None
        end
    end.
*)
  Admitted.

  (** I'd like to make these mutually recursive...**)
  Fixpoint exprUnifyArgs dom (r l : list (expr types)) (s : Subst dom) 
    : option (Subst dom).
(*
    match r in hlist _ ls
      return hlist (expr funcs uL vs) ls -> Subst uR uL vs -> option (Subst uR uL vs)
      with
      | HNil => fun _ s => Some s
      | HCons _ _ x rr => fun l s =>
        match exprUnify x (hlist_hd l) s with
          | None => None
          | Some s => exprUnifyArgs rr (hlist_tl l) s
        end
    end.
*)
  Admitted.


End Unify.