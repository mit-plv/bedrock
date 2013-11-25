Require Import Inv.

Set Implicit Arguments.

Section Body.

  Variable layout : Layout.

  Variable vars temp_vars : list string.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Require Import SemanticsExpr.

  Require Import Semantics.
  Require Import Safe.

  Definition loop_inv cond body k : assert := 
    let s := Syntax.Seq (Syntax.While cond body) k in
    inv_template layout vars temp_vars
      (fun fs v st => 
         Safe fs s v /\
         st#Rv = eval (fst v) cond)
      (fun fs v st v' st' =>
         RunsTo fs s v v' /\
         st'#Sp = st#Sp).

  Require Import ReservedNames.

  Definition frame' := STACK_CAPACITY :: vars ++ temp_vars.
  Definition frame := "rp" :: frame'.
  Definition frame_len := length frame.
  Definition frame_len_w := natToW (4 * frame_len).
  Definition get_var x := variableSlot x frame'.

  Definition afterCall ret k : assert :=
    inv_template layout vars temp_vars
      (fun fs v st => 
         Safe fs k v)
      (fun fs v st v' st' =>
         let v := (upd_option (fst v) ret st#Rv, snd v) in
         RunsTo fs k v v' /\
         let old_sp := st#Sp ^- frame_len_w in
         st'#Sp = old_sp).

  Require Import CompileExpr.

  Definition compile_expr e n := CompileExpr.compile vars temp_vars e n imports_global modName.

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

  Definition SaveRv var := Strline (IL.Assign (variableSlot var vars) (RvLval (LvReg Rv)) :: nil).

  Fixpoint compile_exprs exprs base :=
    match exprs with
      | nil => nil
      | x :: xs => compile_expr x base :: SaveRv (temp_name base) :: compile_exprs xs (S base)
    end.

  Fixpoint put_args base (target : nat) n :=
    match n with
      | 0 => nil
      | S n' =>
        Assign (LvMem (Rv + target)%loc) (get_var (temp_name base))
               :: put_args (1 + base) (4 + target) n'
    end.

  Definition CheckStack (n : nat) cmd :=
    Structured.If_ imports_global n Le (get_var STACK_CAPACITY) cmd
                   (Diverge_ imports modName).

  Definition SaveRet var :=
    match var with
      | None => Skip
      | Some x => SaveRv x
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
        let init_frame := 2 + Datatypes.length args in
        CheckStack 
          init_frame
          (Seq
             ((compile_expr f 0) 
                :: SaveRv (temp_name 0)
                :: compile_exprs args 1 ++
                Strline
                ((Binop Rv Sp Plus frame_len_w)
                   :: Binop (LvMem (Rv + $ (4))%loc) (get_var STACK_CAPACITY) Minus init_frame
                   :: put_args 1 8 (Datatypes.length args) ++
                   Assign Rv (get_var (temp_name 0))
                   :: Binop Sp Sp Plus frame_len_w :: nil)
                :: Structured.ICall_ imports modName Rv (afterCall var k)
                :: Strline (Binop Sp Sp Minus frame_len_w :: nil)
                :: SaveRet var :: nil))
    end.

End Body.