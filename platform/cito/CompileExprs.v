Require Import AutoSep.
Require Import SyntaxExpr.

Set Implicit Arguments. 

Section TopLevel.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable exprs : list Expr.

  Variable base dst : nat.

  Definition is_state sp vs temps dst_buf : HProp :=
    (locals vars vs 0 (sp ^+ $8) *
     array temps (sp ^+ $8 ^+ $(length vars)) *
     array dst_buf (sp ^+ $ dst))%Sep.

  Definition new_pre : assert := 
    x ~> ExX, Ex vs, Ex temps, Ex dst_buf,
    ![^[is_state x#Sp vs temps dst_buf] * #0]x /\
    [| length temps = temp_size /\
       length exprs <= length dst_buf |].

  Require Import SemanticsExpr.
  Require Import DepthExpr.
  Require Import Max.

  Definition depth := max_list (map depth exprs) 0.

  Require CompileExpr.
  Require Import ListFacts.

  Local Open Scope nat.

  Definition runs_to x_pre x := 
    forall specs other vs temps dst_buf,
      interp specs (![is_state x_pre#Sp vs temps dst_buf * other ] x_pre) ->
      length temps = temp_size /\
      length exprs <= length dst_buf /\
      Regs x Sp = x_pre#Sp /\
      exists changed,
        interp specs (![is_state (Regs x Sp) vs (upd_sublist temps base changed) (upd_sublist dst_buf 0 (map (eval vs) exprs)) * other ] (fst x_pre, x)) /\
        length changed <= depth.

  Definition post (pre : assert) := 
    st ~> Ex st_pre, 
    pre (fst st, st_pre) /\
    [| runs_to (fst st, st_pre) (snd st) |].

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Require Import FreeVarsExpr.
  Require Import StringSet.
  Require Import SetUtil.
  Require Import Union.

  Definition in_scope := 
    Subset (union_list (map free_vars exprs)) (to_set vars) /\
    base + depth <= temp_size.

  Definition verifCond pre := imply pre new_pre :: in_scope :: nil.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Skip := Straightline_ imports modName nil.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition Strline := Straightline_ imports modName.

  Definition SaveRv lv := Strline (IL.Assign lv (RvLval (LvReg Rv)) :: nil).

  Definition stack_slot (n : nat) := LvMem (Sp + n)%loc.

  Definition compile_expr e n := CompileExpr.compile vars temp_size e n imports_global modName.

  Fixpoint do_compile exprs base dst :=
    match exprs with
      | nil => nil
      | x :: xs => 
        compile_expr 
          x base 
          :: SaveRv (stack_slot dst) 
          :: do_compile xs base (4 + dst)
    end.

  Definition body := Seq (do_compile exprs base dst).

  Require Import Wrap.

  Definition compile : cmd imports modName.
    refine (Wrap imports imports_global modName body post verifCond _ _).
    admit.
    admit.
 Defined.

End TopLevel.