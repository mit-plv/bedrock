Require Import Semantics.
Require Import Syntax SemanticsExpr.
Require Import Memory IL List.

Section fs.

  Variable fs : W -> option Callee.

  CoInductive Safe : Stmt -> State -> Prop :=
  | Skip : 
      forall v, Safe Syntax.Skip v
  | Seq : 
      forall a b v, 
        Safe a v ->
        (forall v', RunsTo fs a v v' -> Safe b v') -> 
        Safe (Syntax.Seq a b) v
  | IfTrue : 
      forall cond t f v, 
        wneb (eval (fst v) cond) $0 = true -> 
        Safe t v -> 
        Safe (Syntax.If cond t f) v
  | IfFalse : 
      forall cond t f v, 
        wneb (eval (fst v) cond) $0 = false -> 
        Safe f v -> 
        Safe (Syntax.If cond t f) v
  | WhileTrue : 
      forall cond body v, 
        let statement := While cond body in
        wneb (eval (fst v) cond) $0 = true -> 
        Safe body v ->
        (forall v', RunsTo fs body v v' -> Safe statement v') -> 
        Safe statement v
  | WhileFalse : 
      forall cond body v, 
        wneb (eval (fst v) cond) $0 = false -> 
        Safe (While cond body) v
  | CallInternal : 
      forall var f args v spec,
        let vs := fst v in
        let heap := snd v in
        fs (eval vs f) = Some (Internal spec) ->
        (forall vs_arg, 
           map (Locals.sel vs_arg) (ArgVars spec) = map (eval vs) args 
           -> Safe (Body spec) (vs_arg, heap)) ->
        Safe (Syntax.Call var f args) v
  | CallForeign : 
      forall var f args v spec pairs,
        let vs := fst v in
        let heap := snd v in
        fs (eval vs f) = Some (Foreign spec) ->
        map (eval vs) args = map fst pairs ->
        Forall (heap_match heap) pairs ->
        PreCond spec (map snd pairs) ->
        Safe (Syntax.Call var f args) v.

End fs.
