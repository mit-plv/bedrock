Require Import List String Ascii.

Require Import LabelMap Word IL XCAP.

Set Implicit Arguments.

Global Open Scope string_scope.


Fixpoint wordS sz (w : word sz) : string :=
  match w with
    | WO => ""
    | WS false _ w' => wordS w' ++ "0"
    | WS true _ w' => wordS w' ++ "1"
  end.

Definition binS sz (w : word sz) : string :=
  "0b" ++ wordS w.

Definition regS (r : reg) : string :=
  match r with
    | Sp => "%ebx"
    | Rp => "%ecx"
    | Rv => "%eax"
  end.

Definition tab := String (ascii_of_nat 9) "".
Definition nl := String (ascii_of_nat 10) "".

Definition locS (l : loc) : string :=
  match l with
    | Reg r => "bedrock_heap(" ++ regS r ++ ")"
    | Imm w => binS w ++ "+bedrock_heap"
    | Indir r w => binS w ++ "+bedrock_heap(" ++ regS r ++ ")"
  end.

Definition lvalueS (lv : lvalue) : string :=
  match lv with
    | LvReg r => regS r
    | LvMem l => locS l
  end.

Definition label'S (lab' : label') : string :=
  match lab' with
    | Global s => s
    | Local n => wordS (NToWord 32 n)
  end.

Definition labelS (lab : label) : string :=
  let (mod, blk) := lab in
    mod ++ "_" ++ label'S blk.

Definition rvalueS (rv : rvalue) : string :=
  match rv with
    | RvLval lv => lvalueS lv
    | RvImm w => "$" ++ binS w
    | RvLabel lab => "$" ++ labelS lab
  end.

Definition binopS (o : binop) : string :=
  match o with
    | Plus => "addl"
    | Minus => "subl"
    | Mult => "imull"
  end.

Definition instrS (i : instr) : string :=
  match i with
    | Assign (LvMem l1) (LvMem l2) =>
      tab ++ "movl " ++ locS l2 ++ ",%edx" ++ nl
      ++ tab ++ "movl %edx," ++ locS l1 ++ nl
    | Assign lv rv =>
      tab ++ "movl " ++ rvalueS rv ++ "," ++ lvalueS lv ++ nl
    | Binop lv rv1 o rv2 =>
      tab ++ "movl " ++ rvalueS rv1 ++ ",%edx" ++ nl
      ++ tab ++ binopS o ++ " " ++ rvalueS rv2 ++ ",%edx" ++ nl
      ++ tab ++ "movl %edx," ++ lvalueS lv ++ nl
  end.

Definition testS (t : test) : string :=
  match t with
    | Eq => "z"
    | Ne => "nz"
    | Lt => "b"
    | Le => "na"
  end.

Definition jmpS (j : jmp) : string :=
  match j with
    | Uncond (RvLabel lab) =>
      tab ++ "jmp " ++ labelS lab ++ nl
    | Uncond rv =>
      tab ++ "movl " ++ rvalueS rv ++ ",%edx" ++ nl
      ++ tab ++ "jmp *%rdx" ++ nl
    | Cond (LvMem l1) t (LvMem l2) lab1 lab2 =>
      tab ++ "movl " ++ locS l2 ++ ",%edx" ++ nl
      ++ tab ++ "cmpl %edx," ++ locS l1 ++ nl
      ++ tab ++ "j" ++ testS t ++ " " ++ labelS lab1 ++ nl
      ++ tab ++ "jmp " ++ labelS lab2 ++ nl
    | Cond rv1 t rv2 lab1 lab2 =>
      tab ++ "cmpl " ++ rvalueS rv2 ++ "," ++ rvalueS rv1 ++ nl
      ++ tab ++ "j" ++ testS t ++ " " ++ labelS lab1 ++ nl
      ++ tab ++ "jmp " ++ labelS lab2 ++ nl
  end.

Definition blockS (b : block) : string :=
  let (is, j) := b in
    fold_right (fun i s => instrS i ++ s) (jmpS j) is.

Definition moduleS (m : module) : string :=
  fold_right (fun bl s => let '(lab, (_, b)) := bl in
    labelS lab ++ ":" ++ nl ++ blockS b ++ s) "" (LabelMap.elements m.(Blocks)).

Global Transparent natToWord.
