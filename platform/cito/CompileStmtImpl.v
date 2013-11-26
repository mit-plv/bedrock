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

  Definition loop_inv cond body k : assert := 
    let s := Syntax.Seq (Syntax.While cond body) k in
    inv_template layout vars temp_size
      (fun fs v st => 
         Safe fs s v /\
         st#Rv = eval (fst v) cond)
      (fun fs v st v' st' =>
         RunsTo fs s v v' /\
         st'#Sp = st#Sp).

  Definition vars_start := 4 * 2.
  Definition temp_start := vars_start + 4 * length vars.
  Definition get_stack_capacity := LvMem (Sp + 4)%loc.
  Definition get_var x := LvMem (Sp + (vars_start + variablePosition vars x)%nat)%loc.
  Definition get_temp n := LvMem (Sp + (temp_start + 4 * n)%nat)%loc.
  Definition frame_len := temp_start + 4 * temp_size.
  Definition frame_len_w := natToW frame_len.

  Definition afterCall ret k : assert :=
    inv_template layout vars temp_size
      (fun fs v st => 
         Safe fs k v)
      (fun fs v st v' st' =>
         let v := (upd_option (fst v) ret st#Rv, snd v) in
         RunsTo fs k v v' /\
         let old_sp := st#Sp ^- frame_len_w in
         st'#Sp = old_sp).

  Require Import CompileExpr.

  Definition compile_expr e n := CompileExpr.compile vars temp_size e n imports_global modName.

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

  Fixpoint compile_exprs exprs base :=
    match exprs with
      | nil => nil
      | x :: xs => compile_expr x base :: SaveRv (get_temp base) :: compile_exprs xs (S base)
    end.

  Fixpoint put_args base (target : nat) n :=
    match n with
      | 0 => nil
      | S n' =>
        Assign (LvMem (Rv + target)%loc) (get_temp base)
               :: put_args (1 + base) (4 + target) n'
    end.

  Definition CheckStack (n : nat) cmd :=
    Structured.If_ imports_global n Le get_stack_capacity cmd
                   (Diverge_ imports modName).

  Definition SaveRet var :=
    match var with
      | None => Skip
      | Some x => SaveRv (get_var x)
    end.

  Require Import Notations.
  Local Open Scope stmt.
  Local Open Scope nat.

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
        let init_frame_len := 2 + length args in
        CheckStack 
          init_frame_len
          (Seq
             ((compile_expr f 0) 
                :: SaveRv (get_temp 0)
                :: compile_exprs args 1 ++
                Strline
                ((Binop Rv Sp Plus frame_len_w)
                   :: Binop (LvMem (Rv + $ (4))%loc) get_stack_capacity Minus init_frame_len
                   :: put_args 1 8 (length args) ++
                   Assign Rv (get_temp 0)
                   :: Binop Sp Sp Plus frame_len_w :: nil)
                :: Structured.ICall_ imports modName Rv (afterCall var k)
                :: Strline (Binop Sp Sp Minus frame_len_w :: nil)
                :: SaveRet var :: nil))
    end.

End Body.