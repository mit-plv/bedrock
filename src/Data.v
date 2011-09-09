(** Data Structures
 ** This file contains efficiently computable implementations of data
 ** structures aimed at being used in reflective simplification procedures.
 **)
Require Import List.

Section FSet.
  Variable T : Type.

  Definition set := list T.

  Definition set_empty : set := nil.
End FSet.

Section FMap.
  Variable K : Type.
  Variable V : K -> Type.
  
  Definition fmap := list (sigT V).

  Variable Keq_dec : forall (a b : K), {a = b} + {a <> b}.

  Fixpoint lookup (k : K) (m : fmap): option (V k) :=
    match m with
      | nil => None
      | existT a b :: r => 
        match Keq_dec a k in { _ } + { _ } return option (V k) with
          | left pf => match pf in _ = k return option (V k) with
                         | refl_equal => Some b
                       end
          | right _ => lookup k r
        end
    end.

  Fixpoint insert (k : K) (v : V k) (m : fmap) : fmap :=
    match m with
      | nil => @existT K V k v :: nil
      | existT a b :: r => 
        match Keq_dec a k with
          | left pf => match pf with
                         | refl_equal => @existT K V k v :: r
                       end
          | right _ => @existT K V a b :: insert k v r
        end
    end.
End FMap.

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