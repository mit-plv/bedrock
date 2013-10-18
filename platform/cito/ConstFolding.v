Require Import Optimizer.
Require Import Syntax.
Require Import SyntaxExpr.

Definition VarToW := string -> option W.

Definition Vars := string -> Prop.

Open Scope type_scope.

(* Info: vars with know value * assigned vars *)
Definition Info := VarToW * Vars.

Fixpoint const_folding_expr (e : Expr) (env : VarToW) : Expr :=
  match e with
    | Var var =>
      match env var with
        | Some w => Const w
        | None => e
      end
    | Const w => e
    | Binop op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match a', b' with
        | Const wa,  Const wb => Const (evalBinop op wa wb)
        | _, _ => Binop op a' b'
      end
    | TestE op a b =>
      let a' := const_folding_expr a env in
      let b' := const_folding_expr b env in
      match a', b' with
        | Const wa,  Const wb => Const (if evalTest op wa wb then $1 else $0)
        | _, _ => TestE op a' b'
      end
  end.

Definition empty_VarToW : VarToW := fun _ => None.

Definition empty_Vars : Vars := fun _ => False.

Variable subtract : VarToW -> Vars -> VarToW.
Infix "-" := subtract.

Variable union : Vars -> Vars -> Vars.
Infix "+" := union.

Variable add : Vars -> string -> Vars.
Infix "%+" := add (at level 60).

Variable VarToW_add : VarToW -> string * W -> VarToW.
Infix "%%+" := VarToW_add (at level 60).

Variable VarToW_del : VarToW -> string -> VarToW.
Infix "%%-" := VarToW_del (at level 60).

Inductive IsZeroResult := 
  | IsZero : IsZeroResult
  | NotZero : Expr -> IsZeroResult.

Definition const_folding_expr_is_zero e env : IsZeroResult :=
  match const_folding_expr e env with
    | Const w =>
      if wneb w $0 then
        NotZero (Const w)
      else
        IsZero
    | c' => NotZero c'
  end.

Fixpoint const_folding (s : Statement) (info : Info) : Statement * Info :=
  match s with
    | Skip => (s, info)
    | Seq a b => 
      let (a', info') := const_folding a info in
      let (b', info'') := const_folding b info' in
      (Seq a' b', info'')
    | Conditional c t f =>
      match const_folding_expr c (fst info) with
        | Const w =>
          if wneb w $0 then
            const_folding t info
          else
            const_folding f info
        | c' =>
          let (t', info_t) := const_folding t (fst info, empty_Vars) in
          let (f', info_f) := const_folding f (fst info, empty_Vars) in
          let vars_with_known_value := fst info - snd info_t - snd info_f in
          let assigned_vars := snd info + snd info_t + snd info_f in
          (Conditional c' t' f', (vars_with_known_value, assigned_vars))
      end
    | Loop c b =>
      match const_folding_expr_is_zero c (fst info) with
        | IsZero =>
            (Skip, info)
        | NotZero c' =>
          let (b', info_b) := const_folding b (fst info, empty_Vars) in
          let vars_with_know_value := fst info - snd info_b in
          let assigned_vars := snd info + snd info_b in
          (Loop c' b', (vars_with_know_value, assigned_vars))
      end          
    | Assignment var e =>
      let assigned_vars := snd info %+ var in
      match const_folding_expr e (fst info) with
        | Const w =>
          let vars_with_known_value := fst info %%+ (var, w) in
          (Assignment var (Const w), (vars_with_known_value, assigned_vars))
        | e' =>
          let vars_with_known_value := fst info %%- var in
          (Assignment var e', (vars_with_known_value, assigned_vars))
      end
    | ReadAt var arr idx =>
      let arr' := const_folding_expr arr (fst info) in
      let idx' := const_folding_expr idx (fst info) in
      (ReadAt var arr' idx', (fst info %%- var, snd info %+ var))
    | WriteAt arr idx e =>
      let arr' := const_folding_expr arr (fst info) in
      let idx' := const_folding_expr idx (fst info) in
      let e' := const_folding_expr e (fst info) in
      (WriteAt arr' idx' e', info)
    | Len var arr =>
      let arr' := const_folding_expr arr (fst info) in
      (Len var arr', (fst info %%- var, snd info %+ var))
    | Malloc var size =>
      let size' := const_folding_expr size (fst info) in
      (Malloc var size', (fst info %%- var, snd info %+ var))
    | Free arr =>
      let arr' := const_folding_expr arr (fst info) in
      (Free arr', info)
    | Syntax.Call f x =>
      let f' := const_folding_expr f (fst info) in
      let x' := const_folding_expr x (fst info) in
      (Syntax.Call f' x', info)
  end.

