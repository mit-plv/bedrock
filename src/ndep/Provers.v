Require Import List.
Require Import Bedrock.ndep.Expr.
Require Import EquivDec.
Require Import Env.

Notation "[ a ]" := (a :: nil).
Notation "[ a ,  b ]" := (a :: b :: nil).
Notation "[ a ,  b ,  c ]" := (a :: b :: c :: nil).
Notation "[ a ,  b ,  c ,  d ]" := (a :: b :: c :: d :: nil).

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

Definition eq_dec_to_seq_dec A (d : forall x y : A, { x = y } + { ~ x = y }) x y : option (x = y)
  := match (d x y) with
       | left pf => Some pf
       | right _ => None
     end.
Implicit Arguments eq_dec_to_seq_dec [A].

Require Import Arith Bool.
Definition type_nat := {| Expr.Eq := eq_dec_to_seq_dec eq_nat_dec |}.
Definition type_bool := {| Expr.Eq := eq_dec_to_seq_dec bool_dec |}.
Definition type_list_bool := {| Expr.Eq := eq_dec_to_seq_dec (list_eq_dec bool_dec) |}.
Definition test_types := [type_nat, type_bool, type_list_bool].
(* 0 => nat, 1 => bool, 2 => list bool *)
Definition tvar_nat := tvType 0.
Definition tvar_bool := tvType 1.
Definition tvar_list_bool := tvType 2.
Definition tvar_empty := tvType 3.
Check Build_signature.
Definition test_eq_sig := Build_signature test_types [tvar_nat, tvar_nat] tvar_bool beq_nat.
Definition test_plus_sig := Build_signature test_types [tvar_nat, tvar_nat] tvar_nat plus.
Fixpoint bin_to_nat (ls : list bool) : nat :=
  match ls with
    | nil => 0
    | false :: ls' => 2 * (bin_to_nat ls')
    | true :: ls' => S (2 * (bin_to_nat ls'))
  end.
Definition test_bin_to_nat_sig := Build_signature test_types [tvar_list_bool] tvar_nat bin_to_nat.
Definition test_constant_false_sig := Build_signature test_types [tvar_empty] tvar_bool (fun _ => false).
Definition test_functions := [test_eq_sig, test_plus_sig, test_bin_to_nat_sig, test_constant_false_sig].
(* 0 => eq, 1 => plus, 2 => bin_to_nat, 3 => fun _ => false *)
Eval compute in (Denotation test_eq_sig).
Eval compute in (functionTypeD (map (tvarD test_types) (Domain test_eq_sig))
         (tvarD test_types (Range test_eq_sig))).

Section AssumptionProver.
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
End AssumptionProver.

Section ReflexivityProver.
  Context {types : list type}.
  Variable fs : functions types.
  Variable eqFun : func.
  
  Definition reflexivityProver : (@ProverT types) := fun hyps goal => 
    match goal with
      | Func f [x, y] => if equiv_dec f eqFun
                           then if expr_seq_dec x y then true else false
                           else false
      | _ => false
    end.

  Check (nth_error test_functions 0).

  Ltac caseDestruct t := destruct t; try discriminate.
  Theorem reflexivityProverOk : ProverCorrect fs reflexivityProver.
    unfold ProverCorrect.
    intros.
    unfold FalseDefault.
    unfold reflexivityProver in H.
    caseDestruct goal.
    repeat caseDestruct l.
    caseDestruct (equiv_dec f eqFun).
    unfold equiv in *.
    caseDestruct (expr_seq_dec e e0).
  Qed.
  
End ReflexivityProver.

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
