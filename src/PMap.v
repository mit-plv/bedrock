(** Data Structures
 ** This file contains efficiently computable implementations of data
 ** structures aimed at being used in reflective simplification procedures.
 ** 
 ** We can't use coq's modular implementations because we have to store
 ** terms and values that depend on contexts which we can not pre-compute.
 **)
Require Import List.
Require Import Env.

Section FSet.
  Variable T : Type.

  Definition set := list T.

  Definition set_empty : set := nil.
End FSet.

Section FMap.
  Variable K : Type.
  Variable V : K -> Type.

  Variable Kcmp : forall (a b : K), option (dcomp a b).

  Inductive dmap : Type :=
  | DM_Empty : dmap
  | DM_Branch : forall k, V k -> dmap -> dmap -> dmap.

  Definition dmap_empty : dmap := DM_Empty.
  
  Definition dmap_is_empty (d : dmap) : bool :=
    match d with
      | DM_Empty => true
      | _ => false
    end.

  Variable k : K.

  Fixpoint dmap_lookup (m : dmap): option (V k) :=
    match m with
      | DM_Empty => None
      | DM_Branch k' v' l r =>
        match Kcmp k' k with
          | None => match dmap_lookup l with
                      | None => dmap_lookup r
                      | Some x => Some x
                    end
          | Some x => match x with
                        | Gt => dmap_lookup l 
                        | Lt => dmap_lookup r
                        | Eq pf => 
                          (** TODO: I don't think this is going to be computable **)
                          match pf in _ = k return option (V k) with
                            | refl_equal => Some v'
                          end
                      end
        end
    end.

  Fixpoint dmap_insert (v : V k) (m : dmap) : dmap :=
    match m with
      | DM_Empty => DM_Branch k v m m 
      | DM_Branch k' v' l r =>
        match Kcmp k' k with
          | Some Gt => DM_Branch k' v' l (dmap_insert v r)
          | _ => DM_Branch k' v' (dmap_insert v l) r
        end
    end.

  Fixpoint insert_right (l r : dmap) : dmap :=
    match l with 
      | DM_Empty => r 
      | DM_Branch k v ll rr =>
        DM_Branch k v ll (insert_right rr r)
    end.
    

  Fixpoint dmap_remove (m : dmap) : option (V k * dmap) :=
    match m with
      | DM_Empty => None
      | DM_Branch k' v' l r =>
        match Kcmp k' k with
          | None => match dmap_remove l with
                      | None => match dmap_remove r with
                                  | Some (res, r') => Some (res, DM_Branch k' v' l r')
                                  | None => None
                                end
                      | Some (res, l') => Some (res, DM_Branch k' v' l' r)
                    end
          | Some x =>
            match x with
              | Gt => match dmap_remove r with
                        | None => None
                        | Some (res,m) => Some (res, DM_Branch k' v' l m)
                      end
              | Lt => match dmap_remove r with
                        | None => None
                        | Some (res,m) => Some (res, DM_Branch k' v' m r)
                      end
              | Eq pf =>
                (** TODO: I don't think this is going to be computable **)
                Some (match pf in _ = t return V t with
                        | refl_equal => v' 
                      end, 
                match l, r with
                  | DM_Empty , _ => r 
                  | _ , DM_Empty => l
                  | _ , _ => insert_right l r
                end)
            end
        end
    end.

  Variable T : Type.
  Variable f : T -> forall k, V k -> T.
  Fixpoint dmap_fold (a : T) (m : dmap) : T :=
    match m with
      | DM_Empty => a
      | DM_Branch k v l r =>
        dmap_fold (dmap_fold (f a k v) l) r
    end.
  
End FMap.

Implicit Arguments dmap_empty [ K V ].
Implicit Arguments dmap_fold [ K V T ].
Implicit Arguments dmap_remove [ K V ].
Implicit Arguments dmap_insert [ K V ].

Section map.
  Variable K : Type.
  Variable V V' : K -> Type.
  Variable f : forall k, V k -> V' k.

  Fixpoint dmap_map  (m : @dmap K V) : @dmap K V' :=
    match m with
      | DM_Empty => DM_Empty _ _
      | DM_Branch k v l r =>
        DM_Branch _ _ k (f _ v) (dmap_map l) (dmap_map r)
    end.
End map.


Section Map.
  Variable K : Type.
  Variable V : Type.

  Variable Kcmp : forall (a b : K), option (dcomp a b).

  Definition fmap := @dmap K (fun _ => V).

  Definition fmap_empty := @dmap_empty K (fun _ => V).

  Definition fmap_lookup (k : K) (m : fmap) := @dmap_lookup _ _ Kcmp k m.

  Definition fmap_insert (k : K) (v : V) (m : fmap) := @dmap_insert _ _ Kcmp k v m.

  Definition fmap_remove (k : K) (m : fmap) := dmap_remove Kcmp k m.

  Definition fmap_fold (T : Type) (f : T -> K -> V -> T) :=
    @dmap_fold K (fun _ => V) T (fun a b c => f a b c).
End Map.

Implicit Arguments fmap_empty [ K V ].
Implicit Arguments fmap_fold [ K V T ].
Implicit Arguments fmap_remove [ K V ].
Implicit Arguments fmap_insert [ K V ].

(*
Section MMap.
  Variable K : Type.
  Variable V : K -> Type.
  
  Definition mmap := list {x : K & set (V x)}.

  Variable Keq_dec : forall (a b : K), {a = b} + {a <> b}.

(*
  Fixpoint lookup (m : mmap) (k : K) : set (V k) :=
    match m with
      | nil => set_empty (V k)
      | existT a b :: r => todo _
        match Keq_dec k a in { _ } + { _ } return set (V k) with
          | left _ => b
          | right _ => todo _
        end
    end.

  Fixpoint insert (m : mmap) (k : K) (v : V) : mmap :=
    match m with
      | nil => (k, v :: nil) :: nil
      | (a,b) :: r => 
        if Keq_dec a k then (a, v :: b) :: r else (a, b) :: insert r k v
    end.
*)

End MMap.
*)
