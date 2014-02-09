Require Import Syntax Semantics SemanticsExpr.
Require Import IL Memory List.

Section Safe_coind.

  Variable R : (W -> option Callee) -> Stmt -> State -> Prop.

  Hypothesis SeqCase : 
    forall fs a b v, 
      R fs (Syntax.Seq a b) v -> 
      R fs a v /\ 
      forall v', RunsTo fs a v v' -> R fs b v'.

  Hypothesis IfCase : 
    forall fs cond t f v, 
      R fs (Syntax.If cond t f) v -> 
      wneb (eval (fst v) cond) $0 = true /\ R fs t v \/ 
      wneb (eval (fst v) cond) $0 = false /\ R fs f v.

  Hypothesis WhileCase : 
    forall fs cond body v, 
      R fs (Syntax.While cond body) v -> 
      (wneb (eval (fst v) cond) $0 = true /\ 
       R fs body v /\ 
       (forall v', RunsTo fs body v v' -> R fs (While cond body) v')) \/ 
      (wneb (eval (fst v) cond) $0 = false).

  Hypothesis CallCase : 
    forall fs var f args v,
      let vs := fst v in
      let heap := snd v in
      R fs (Syntax.Call var f args) v ->
      (exists spec,
         fs (eval vs f) = Some (Internal spec) /\
         (forall vs_arg, 
            map (Locals.sel vs_arg) (ArgVars spec) = map (eval vs) args 
            -> R fs (Body spec) (vs_arg, heap))) \/
      (exists spec pairs,
         fs (eval vs f) = Some (Foreign spec) /\
         map (eval vs) args = map fst pairs /\
         Forall (heap_match heap) pairs /\
         PreCond spec (map snd pairs)).

  Hint Constructors Safe.

  Require Import GeneralTactics.

  Ltac break_pair :=
    match goal with
        V : (_ * _)%type |- _ => destruct V
    end.

  Theorem Safe_coind : forall fs c v, R fs c v -> Safe fs c v.
    cofix; intros; destruct c.

    (* skip *)
    eauto.
    Guarded.

    eapply SeqCase in H; openhyp; eauto.
    Guarded.

    eapply IfCase in H; openhyp; eauto.
    Guarded.

    eapply WhileCase in H; openhyp; eauto.
    Guarded.

    eapply CallCase in H; openhyp; eauto.
    Guarded.
  Qed.

End Safe_coind.

