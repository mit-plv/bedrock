Require Import Expr.
Require Import PMap.
Require Import List.

Set Implicit Arguments.
Set Strict Implicit.

Section Unify.
  Variable types : list type.
  Variable funcs : functions types.
  
  Definition Subst (dom : variables types) uvars vars := 
    @dmap (fin dom) (fun f => expr funcs uvars vars (get _ f)).

  Section Subst.
    Variables dom uvars vars : variables types.
    
    Definition empty_Subst : Subst dom uvars vars :=
      dmap_empty.

    Definition Subst_lookup (k : fin dom) (s : Subst dom uvars vars) :=
      dmap_lookup _ _ (fun a b => Some (finCmp a b)) k s.

    Definition Subst_insert (k : fin dom) (v : _) (s : Subst dom uvars vars) :=
      dmap_insert (fun a b => Some (finCmp a b)) k v s.

    Variable sub : Subst dom uvars vars.

    (** TODO: This isn't done, I'm wondering if it is easier to just make
     ** Subst equal to this hlist
     **)
    Fixpoint env_of_Subst (ls : variables types) 
      : hlist (fun t => option (expr funcs uvars vars t)) ls :=
      match ls as ls 
        return hlist (fun t => option (expr funcs uvars vars t)) ls 
        with
        | nil => HNil 
        | a :: b => 
          let x := sub in
          HCons None (env_of_Subst b)          
      end.
  End Subst.

  Definition get_Eq (t : tvar types) : forall x y : tvarD t, option (x = y) :=
    match t with
      | None => fun _ _ => None
      | Some t => Eq (get _ t)
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

  Fixpoint exprUnify T uL uR vs (r : expr funcs uR vs T) :
    expr funcs uL vs T -> Subst uR uL vs -> option (Subst uR uL vs) :=
    match r in expr _ _ _ T 
      return expr funcs uL vs T -> Subst uR uL vs -> option (Subst uR uL vs) 
      with
      | Const t v => fun l =>
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
            Some (Subst_insert u l s)
          | Some r =>
            if exprEq l r then Some s else None
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

  (** I'd like to make these mutually recursive...**)
  Fixpoint exprUnifyArgs uL uR vs ls (r : hlist (expr funcs uR vs) ls) {struct r} 
    : hlist (expr funcs uL vs) ls -> Subst uR uL vs -> option (Subst uR uL vs) :=
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

(*
  Definition subst T (e : expr funcs (unif ++ vars) T) (s : Subst)
    : expr funcs (varsL ++ vars) T.
    revert s; revert e; revert T.
    About hlist_map.
    refine (fix subst T (e : expr funcs (unif ++ vars) T) (s : Subst)
      : expr funcs (varsL ++ vars) T := 
      match e in expr _ _ T return expr funcs (varsL ++ vars) T with
        | Const t x =>
          Const funcs _ t x
        | Var v =>
          match s v with
            | Some _ => _
            | None => Var _ v
          end
        | Func f a =>
          let a' := 
            @hlist_map _ _ (expr funcs (varsL ++ vars)) (fun t (x : expr funcs (unif ++ vars) t) => subst t x s) _ a 
          in
          Func f a'
      end).
*)

End Unify.