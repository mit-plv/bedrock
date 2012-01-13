Require Import List.
Require Import Bedrock.ndep.Expr.
Require Import EquivDec.
Require Import DepList.

Section ProverT.
  Variable types : list type.
  Variable fs : functions types.

  Definition ProverT : Type := forall 
    (hyps : list (@expr types))
    (goal : @expr types),
    AllProvable fs nil nil hyps ->
    option (Provable fs nil nil goal).
  (* It actually might be more correct for this to be 
   * option (AllProvable fs nil nil hyps -> Provable fs nil nil goal) 
   * but that is harder to program with
   *)

  (* the non-dependent prover should be *)
  Record NProverT : Type :=
  { prove : forall  (hyps : list (@expr types)) (goal : @expr types), bool
  ; prove_correct : 
    forall hyps goal, 
    prove hyps goal = true ->
    AllProvable fs nil nil hyps ->
    Provable fs nil nil goal
  }.

End ProverT.

Section Prover.
  Variable types : list type.
  Variable fs : functions types.

  Fixpoint assumptionProver hyps (goal : expr types) 
    : AllProvable fs nil nil hyps 
    -> option (Provable fs nil nil goal) :=
    match hyps with
      | nil => fun _ => None
      | exp :: b => fun pfHyps : AllProvable fs nil nil (exp :: b) =>
        match seq_dec exp goal with
          | Some pf => Some match pf in _ = t return Provable fs nil nil t with
                              | refl_equal => proj1 pfHyps
                            end
          | None => assumptionProver b goal (proj2 pfHyps)
        end
    end.
End Prover.

Section BabyOmega.
  Context {types : list type}.
  Context {fs : forall types', functions (types' ++ types)}.

  Definition types' : list type :=
    {| Impl := nat; Expr.Eq := fun x y : nat => match Peano_dec.eq_nat_dec x y with left Heq => Some Heq | _ => None end |} :: types.

  Definition fs' : functions types' :=
    (@Sig types' (tvType 0 :: tvType 0 :: nil) tvProp (@eq nat)) ::
    (@Sig types' (tvType 0 :: tvType 0 :: nil) (tvType 0) plus) ::
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