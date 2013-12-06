Require Import Inv.

Set Implicit Arguments.

Section Body.

  Variable layout : Layout.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Require Import SemanticsExpr.

  Require Import Semantics.
  Require Import Safe.

  Definition stack_slot n := LvMem (Sp + (4 * n)%nat)%loc.
  Definition vars_start := 4 * 2.
  Definition temp_start := vars_start + 4 * length vars.
  Definition var_slot x := LvMem (Sp + (vars_start + variablePosition vars x)%nat)%loc.
  Definition temp_slot n := LvMem (Sp + (temp_start + 4 * n)%nat)%loc.
  Definition frame_len := temp_start + 4 * temp_size.
  Definition frame_len_w := natToW frame_len.
  Definition callee_stack_start := frame_len.
  Definition callee_stack_slot n := LvMem (Sp + (callee_stack_start + 4 * n)%nat)%loc.

  Definition loop_inv cond body k : assert := 
    let s := Syntax.Seq (Syntax.While cond body) k in
    inv_template layout vars temp_size
      (fun fs v st => 
         Safe fs s v /\
         st#Rv = eval (fst v) cond)
      (fun fs v st v' =>
         RunsTo fs s v v')
      (fun st => st#Sp).

  Definition after_call ret k : assert :=
    inv_template layout vars temp_size
      (fun fs v st => 
         let v := (upd_option (fst v) ret st#Rv, snd v) in
         Safe fs k v)
      (fun fs v st v' =>
         let v := (upd_option (fst v) ret st#Rv, snd v) in
         RunsTo fs k v v')
      (fun st => st#Sp ^- frame_len_w).

  Require CompileExpr.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Strline := Straightline_ imports modName.

  Definition Skip := Skip_ imports modName.

  Definition If__ := Structured.If_ imports_global.

  Definition While__ := Structured.While_ imports_global.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition SaveRv lv := Strline (IL.Assign lv (RvLval (LvReg Rv)) :: nil).

  Definition CheckExtraStack (n : nat) cmd :=
    Seq2 
      (Strline (IL.Assign Rv (stack_slot 1) :: nil))
      (Structured.If_ imports_global n Le Rv cmd
                      (Diverge_ imports modName)).

  Definition SaveRet var :=
    match var with
      | None => Skip
      | Some x => SaveRv (var_slot x)
    end.

  Definition compile_expr e n := CompileExpr.compile vars temp_size e n imports_global modName.

  Require CompileExprs.

  Definition compile_exprs es n dst := CompileExprs.compile vars temp_size es n dst imports_global modName.

  Require Import Notations.
  Local Open Scope stmt.
  Local Open Scope nat.

  Definition expose_callee_stack (args : list SyntaxExpr.Expr) :=
    if Compare_dec.zerop (List.length args) then
      Skip
    else
      Strline (IL.Assign Rv (LvMem (Sp + (callee_stack_start + 8)%nat)%loc) :: nil).

  Fixpoint compile s k :=
    match s with
      | Syntax.Skip => 
        Skip
      | a ;; b => 
        Seq2 (compile a (b;; k)) 
             (compile b k)
      | Syntax.If cond t f => 
        Seq2 (compile_expr cond 0)
             (If__ Rv Ne (natToW 0) (compile t k) (compile f k))
      | While (cond) {{body}} =>
        Seq2 (compile_expr cond 0)
             (While__ (loop_inv cond body k) Rv Ne (natToW 0)
                      (Seq2 (compile body (While (cond) {{body}};; k))
                            (compile_expr cond 0)))
      | Syntax.Call var f args =>
        let callee_frame_len := 2 + length args in
        CheckExtraStack 
          callee_frame_len
          (Seq
             (expose_callee_stack args
                :: compile_exprs args 0 (callee_stack_start + 8)
                :: compile_expr f 0
                :: Strline
                (Binop 
                   (callee_stack_slot 1) (stack_slot 1) Minus callee_frame_len
                   :: Binop Sp Sp Plus frame_len_w :: nil)
                :: Structured.ICall_ imports modName Rv (after_call var k)
                :: Strline (Binop Sp Sp Minus frame_len_w :: nil)
                :: SaveRet var :: nil))
    end.

End Body.