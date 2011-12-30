Require Import List.
Require Import Bedrock.ndep.Expr.
Require Import EquivDec.
Require Import Env.

Section ProverT.
  Context {types : list type}.
  Variable fs : functions types.


  Definition FalseDefault (e : expr types) : Type :=
    match @exprD types fs nil nil e tvProp with
      | None => False
      | Some p => p
    end.

  Definition ProverT : Type := forall 
    (hyps : list (@expr types))
    (goal : @expr types),
    hlist FalseDefault hyps ->
    option (FalseDefault goal).
  
End ProverT.


Section Prover.
  Variable types : list type.
  Variable fs : functions types.

  Fixpoint assumptionProver hyps (goal : expr types) : hlist (FalseDefault fs) hyps -> option (FalseDefault fs goal) :=
    match hyps with
      | nil => fun _ => None
      | exp :: b => fun pfHyps =>
        match seq_dec exp goal with
          | Some pf => Some match pf in _ = t return FalseDefault fs t with
                              | refl_equal => hlist_hd pfHyps
                            end
          | None => assumptionProver b goal (hlist_tl pfHyps)
        end
    end.
End Prover.

Section BabyOmega.
  Context {types : list type}.
  Context {fs : forall types', functions (types' ++ types)}.

  Definition types' : list type :=
    {| Impl := nat; Expr.Eq := fun x y : nat => match Peano_dec.eq_nat_dec x y with left Heq => Some Heq | _ => None end |} :: types.

  Definition fs' : functions types' :=
    (@Build_signature types' (tvType 0 :: tvType 0 :: nil) tvProp (@eq nat)) ::
    (@Build_signature types' (tvType 0 :: tvType 0 :: nil) (tvType 0) plus) ::
    fs (_ :: nil).

  Definition BabyOmega : @ProverT types' fs'.
    red.
    refine (fun _ goal _ => None).
(*
      match goal in expr _ _ _ T return option (match T return expr _ _ _ T -> Type with
                                                | tvProp => fun goal => exprD HNil HNil goal
                                                | _ => fun _ => Empty_set
                                              end goal) with
        | Func f args =>
          finIfz f DMatch
            (fun args => hlistDestruct args (DMatch' _) 
              (fun x y => if seq_dec x y then Some _ else None))
            (fun _ _ => None) args
        | _ => None
      end);
    try abstract congruence.
*)
    Defined.
End BabyOmega.