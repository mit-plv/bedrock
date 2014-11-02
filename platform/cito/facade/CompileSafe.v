Set Implicit Arguments.

Require Import Facade.
Require Import Memory IL.
Require Import GLabel.

Require Import String.
Local Open Scope string_scope.
Require Import StringMap.
Import StringMap.
Require Import StringMapFacts.
Import FMapNotations.
Local Open Scope fmap_scope.
Require Import List.
Require Import ListFacts4.
Local Open Scope list_scope.

Section Safe_coind.

  Variable ADTValue : Type.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Sca := (@SCA ADTValue).

  Variable env : Env.

  Variable R : Stmt -> State -> Prop.

  Hypothesis SeqCase : forall a b st, R (Seq a b) st -> R a st /\ forall st', RunsTo env a st st' -> R b st'.

  Hypothesis IfCase : forall cond t f st, R (If cond t f) st -> (is_true st cond /\ R t st) \/ (is_false st cond /\ R f st).

  Hypothesis WhileCase : 
    forall cond body st, 
      let loop := While cond body in 
      R loop st -> 
      (is_true st cond /\ R body st /\ (forall st', RunsTo env body st st' -> R loop st')) \/ 
      (is_false st cond).

  Hypothesis AssignCase :
    forall x e st,
      R (Facade.Assign x e) st ->
      not_mapsto_adt x st = true /\
      exists w, eval st e = Some (Sca w).

  Hypothesis LabelCase : 
    forall x lbl st,
      R (Label x lbl) st -> 
      not_mapsto_adt x st = true /\
      exists w, Label2Word env lbl = Some w.

  Hypothesis CallCase : 
    forall x f args st,
      R (Call x f args) st ->
      NoDup args /\
      not_mapsto_adt x st = true /\
      exists f_w input, 
        eval st f = Some (Sca f_w) /\
        mapM (sel st) args = Some input /\
        ((exists spec,
            Word2Spec env f_w = Some (Axiomatic spec) /\
            PreCond spec input) \/
         (exists spec,
            Word2Spec env f_w = Some (Operational _ spec) /\
            length args = length (ArgVars spec) /\
            let callee_st := make_map (ArgVars spec) input in
            R (Body spec) callee_st /\
            (forall callee_st',
               RunsTo env (Body spec) callee_st callee_st' ->
               sel callee_st' (RetVar spec) <> None /\
               no_adt_leak input (ArgVars spec) (RetVar spec) callee_st'))).
  
  Hint Constructors Safe.

  Require Import GeneralTactics.

  Theorem Safe_coind : forall c st, R c st -> Safe env c st.
    cofix; intros; destruct c.

    solve [eauto].
    Guarded.

    solve [eapply SeqCase in H; openhyp; eapply SafeSeq; eauto].
    Guarded.

    solve [eapply IfCase in H; openhyp; eauto].
    Guarded.

    solve [eapply WhileCase in H; openhyp; eauto].
    Guarded.

    solve [eapply CallCase in H; openhyp; simpl in *; intuition eauto].
    Guarded.

    solve [eapply LabelCase in H; openhyp; eauto].
    Guarded.

    solve [eapply AssignCase in H; openhyp; eauto].
  Qed.

End Safe_coind.

Require Import ADT.

Module Make (Import A : ADT).

  Require Import Compile.
  Module CompileMake := Compile.Make A.
  Module Cito := CompileMake.Cito.
  Require Semantics.

  Notation RunsTo := (@RunsTo ADTValue).
  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).
  Notation Adt := (@ADT ADTValue).

(*
  Theorem compile_runsto : 
    forall t t_env t_st t_st', 
      Cito.RunsTo t_env t t_st t_st' -> 
      forall s, 
        t = compile s -> 
        (* h1 : the heap portion that this program is allowed to change *)
        forall h1, 
          h1 <= snd t_st -> 
          forall s_st, 
            related s_st (fst t_st, h1) -> 
            forall s_env, 
              t_env = compile_env s_env -> 
              Safe s_env s s_st -> 
              exists s_st', 
                RunsTo s_env s s_st s_st' /\ 
                (* h2 : the frame heap (the outside portion that won't be touched by this program *)
                let h2 := snd t_st - h1 in 
                (* the frame heap will be intacked in the final state *)
                h2 <= snd t_st' /\ 
                (* variables not appearing as LHS won't change value in Cito state *)
                (forall x, ~ List.In x (assigned s) -> Locals.sel (fst t_st) x = Locals.sel (fst t_st') x) /\
                (* newly allocated ADT objects during this program's execution won't collide with the frame heap *)
                (forall x, is_mapsto_adt x s_st = false \/ is_mapsto_adt x s_st = true /\ Locals.sel (fst t_st) x <> Locals.sel (fst t_st') x -> is_mapsto_adt x s_st' = true -> ~ In (Locals.sel (fst t_st') x) h2) /\
                (* main result: final source-level and target level states are related *)
                related s_st' (fst t_st', snd t_st' - h2).
 *)

End Make.