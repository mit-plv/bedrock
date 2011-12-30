Require Import List.
Require Import Bedrock.dep.Expr.
Require Import EquivDec.

(** TODO: This is going to be interesting...
Section Unify.
  Variable types : list type.
  Variable fs : functions types.

  Definition subst vars vars' :=  hlist (fun t => option (expr fs vars' t)) vars.

  Fixpoint unbound vars vars' (sub : hlist (fun t => option (expr fs vars' t)) vars) : list (tvar types) :=
    match sub with
      | HNil => nil
      | HCons _ _ (Some _) r => unbound _ _ r
      | HCons x _ None r => x :: (unbound _ _ r)
    end.


  Fixpoint unify T vars vars' (p : expr fs (vars' ++ vars) T) (e : expr fs vars T) 
    (sub : subst vars') :
    (expr fs (vars' ++ vars) T * subst vars').
    match p with
      | Const _ _ => _
    end.

End Unify.
**)

Section Prover.
  Variable types : list type.
  Variable fs : functions types.

Definition assumptionProver : ProverT fs.
  red.
  refine (fix assumptionProver hyps (goal : expr fs nil nil tvProp) : hlist (fun e => @exprD _ fs _ _ HNil HNil tvProp e) hyps -> option (exprD HNil HNil goal) :=
    match hyps with
      | nil => fun _ => None
      | exp :: b => fun pfHyps => 
(*        match vs as vs return forall exp : expr fs vs None, hlist (@qexprD _ fs) (existT (fun vs => expr fs vs None) vs exp :: b) -> _ with
          | nil => fun exp pfHyps => 
          *)
        if seq_dec goal exp then Some _ else assumptionProver b goal (hlist_tl pfHyps)
(*          | _ => fun _ pfHyps => assumptionProver b goal (hlist_tl pfHyps)
        end exp
*)
    end);
  clear assumptionProver;
  try abstract (subst;
    repeat match goal with 
             | [ H : hlist _ nil |- _ ] => clear H
             | [ H : hlist _ (_ :: _) |- _ ] => 
               generalize (hlist_hd H); unfold qexprD; generalize (hlist_tl H); simpl; clear H; do 2 intro
           end; auto). 
Defined.
End Prover.


Section BabyOmega.
  Context {types : list type}.
  Context {fs : forall types', functions (types' ++ types)}.

  Require Import Arith.

  Definition types' := {| Impl := nat; Eq := fun x y => match eq_nat_dec x y with left Heq => Some Heq | _ => None end |} :: types.
  Definition fs' : functions types' :=
    {| Domain := tvTrans FO :: tvTrans FO :: nil;
      Range := tvProp; Denotation := eq |}
    :: {| Domain := (tvTrans FO :: tvTrans FO :: nil) : list (tvar types');
      Range := tvTrans FO; Denotation := plus |}
    :: fs (_ :: nil).

  Definition DMatch' f args :=
    option (match Range (get fs' f) as T return (expr fs' nil nil T -> Type) with
              | tvTrans f0 => fun _ : expr fs' nil nil (tvTrans f0) => Empty_set
              | tvProp => fun goal : expr fs' nil nil tvProp  => exprD HNil HNil goal
            end (Func f args)).

  Definition DMatch (f : fin fs') : Type :=
    forall args : hlist (expr fs' nil nil) (Domain (get fs' f)), DMatch' f args.

  Definition BabyOmega : @ProverT types' fs'.
    red.
    refine (fun _ goal _ =>
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

(*
    intro. apply (TagDIf c (fun c => forall args : hlist (expr fs' nil) (Domain (get fs' (FS c))), option (match Range (get fs' (FS c)) as T return (expr fs' nil T -> Type) with
      | Some f0 => fun _ : expr fs' nil (Some f0) => Empty_set
      | None => fun goal0 : expr fs' nil None => exprD HNil goal0
      end (Func (FS c) args)))). simpl.
    admit. intros. apply None.
*)
    Defined.
End BabyOmega.