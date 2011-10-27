(** Reusable Ltac procedures:
 ** - reflecting function applications
 ** - list lookup
 ** - 
 **)
Require Import List Env.

Set Implicit Arguments.

Section PartialApply.
  Fixpoint funtype (ls : list Type) (r : Type) : Type :=
    match ls with 
      | nil => r
      | a :: b => a -> funtype b r
    end.

  Fixpoint apply_ls (ls : list Type) (T : Type) (R : T -> Type) (V : T)
    : funtype ls (forall x : T, R x) -> funtype ls (R V) :=
    match ls with
      | nil => fun F => F V
      | a :: b => fun F => fun x : a => apply_ls b R V (F x)
    end.
End PartialApply.

(** Reflect an application
 ** - reflects all the non-dependent arguments of e into a tuple
 ** - the tuple and the resulting function (may be partially applied)
 **   are passed to the continuation [cc]
 **) 
Ltac refl_app cc e := 
  let rec refl cc e As :=
    match e with
      | ?A ?B =>
        let Ta := type of A in
        match type of A with
          | _ -> ?TT => 
            let As := constr:((B, As)) in
            let Tb := type of B in
            let cc f Ts args := 
              let Ts' := constr:(Ts ++ (Tb : Type) :: nil) in
              cc f Ts' args
            in 
            refl cc A As
          | forall x : ?T1, @?T2 x => 
            let cc f Ts args := 
              let Tb  := type of B in
              let f'  := eval simpl in (@apply_ls Ts T1 T2 B f) in
              cc f' Ts args
            in
            refl cc A As
        end
      | _ =>
        let Ts := constr:(@nil Type) in
        cc e Ts As
    end
  in
  let b := constr:(tt) in
  refl cc e b.

