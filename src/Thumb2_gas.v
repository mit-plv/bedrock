(* Thumb2_gas -- Thumb-2 code generator *)

Require Import List.  Import ListNotations.

Require Import FastString.

(* Function application operator, à la Haskell *)
Notation "f $ x" := (f x) (at level 100, right associativity, only parsing).


(* Partial Thumb-2 machine definition *)
Module Thumb.
  Require Import Ascii.

  Require Import Memory.
  Require Import Word.

  Local Open Scope nat.
  Local Open Scope string.
  Set Implicit Arguments.

  Inductive register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | PC.

  Inductive litOrLabel :=
  | Literal : W -> litOrLabel
  | Label : string -> litOrLabel.

  Inductive condition := EQ | NE | MI.

  Inductive instruction :=
  | (* Yes, Thumb supports more than register-register moves.  For those, use
    LdrEq, which triggers GAS's <<ldr=>> pseudo-opcode.  See
    <<https://sourceware.org/binutils/docs/as/ARM-Opcodes.html>>. *)
    Mov : register -> register -> instruction
  | LdrEq : register -> litOrLabel -> instruction
  | Ldr : register -> register -> instruction
  | LdrB : register -> register -> instruction
  | Str : register -> register -> instruction
  | StrB : register -> register -> instruction
  | Add : register -> register -> register -> instruction
  | Sub : register -> register -> register -> instruction
  | Mul : register -> register -> register -> instruction
  | Branch : string -> instruction
  | Cmp : register -> register -> instruction
  | CondBranch : condition -> string -> instruction.


  Module Show.
    Definition tab := String (ascii_of_nat 9) "".
    Definition newline := String (ascii_of_nat 10) "".

    Fixpoint wordS sz (w : word sz) : string :=
      match w with
        | WO => ""
        | WS false _ w' => wordS w' ++ "0"
        | WS true _ w' => wordS w' ++ "1"
      end.

    Definition register r :=
      match r with
        | R0 => "r0"
        | R1 => "r1"
        | R2 => "r2"
        | R3 => "r3"
        | R4 => "r4"
        | R5 => "r5"
        | R6 => "r6"
        | PC => "pc"
      end.

    Definition litOrLabel x :=
      match x with
        | Literal lit => "0b" ++ wordS lit
        | Label s => s
      end.

    Definition condition (cond : condition) : string :=
      match cond with
        | EQ => "eq"
        | NE => "ne"
        | MI => "mi"
      end.

    Definition mnemonic (name : string) (operands : list string) : string :=
      tab ++ name ++ " " ++ intercalate ", " operands ++ newline.

    Definition instruction (instr : instruction) : string :=
      match instr with
        | Mov rd rn => mnemonic "mov" $ map register [rd; rn]
        | LdrEq rd x => mnemonic "ldr" [register rd; "=" ++ litOrLabel x]
        | Ldr rd rn => mnemonic "ldr" [register rd; "[" ++ register rn ++ "]"]
        | LdrB rd rn => mnemonic "ldrb" [register rd; "[" ++ register rn ++ "]"]
        | Str rd rn => mnemonic "str" [register rd; "[" ++ register rn ++ "]"]
        | StrB rd rn => mnemonic "strb" [register rd; "[" ++ register rn ++ "]"]
        | Add rd rn rm => mnemonic "add" $ map register [rd; rn; rm]
        | Sub rd rn rm => mnemonic "sub" $ map register [rd; rn; rm]
        | Mul rd rm rs => mnemonic "mul" $ map register [rd; rm; rs]
        | Branch label => mnemonic "b" [label]
        | Cmp rn rm => mnemonic "cmp" $ map register [rn; rm]
        | CondBranch cond label => mnemonic ("b" ++ condition cond) [label]
      end.

  End Show.

End Thumb.


Require IL.
Require Import LabelMap.
Require Import Labels.
Require Import Memory.
Require Import Word.
Require XCAP.

Local Open Scope string.

Fixpoint wordS {sz} (w : word sz) : string :=
  match w with
    | WO => ""
    | WS false _ w' => wordS w' ++ "0"
    | WS true _ w' => wordS w' ++ "1"
  end.

Definition binS {sz} (w : word sz) : string :=
  "0b" ++ wordS w.

Definition regS (r : IL.reg) : Thumb.register :=
  match r with
    | IL.Sp => Thumb.R0
    | IL.Rp => Thumb.R1
    | IL.Rv => Thumb.R2
  end.

Definition labelS (lab : label) : string :=
  let (mod, blk) := lab in
  mod ++ "_" ++ match blk with
                  | Global s => s
                  | Local n => wordS $ NToWord 32 n
                end.

Local Close Scope string.  Local Open Scope list.

(* Apply [mnemonic] to the register [reg] and the memory location described by
[loc] to execute a load or a store.  Use [tmp1] and [tmp2] as scratchpad
registers; each must be different from [reg] (and the other). *)
Definition memS (tmp : Thumb.register * Thumb.register)
                (mnemonic : Thumb.register
                            -> Thumb.register
                            -> Thumb.instruction)
                (reg : Thumb.register)
                (loc : IL.loc)
                : list Thumb.instruction
                :=
  let (tmp1, tmp2) := tmp in
  let heap := Thumb.Label "bedrock_heap" in
  match loc with
    | IL.Reg r => [ Thumb.LdrEq tmp1 heap;
                    Thumb.Add tmp1 tmp1 $ regS r;
                    mnemonic reg tmp1]
    | IL.Imm w => (* Thumb's <<add>> does support immediates baked into the
                  instruction, but they can only be 13 bits wide.  Better to
                  assume the immediate is too large and just put it in a
                  register. *)
                  [ Thumb.LdrEq tmp1 heap;
                    Thumb.LdrEq tmp2 $ Thumb.Literal w;
                    Thumb.Add tmp1 tmp1 tmp2;
                    mnemonic reg tmp1 ]
    | IL.Indir r w => (* See note in previous case. *)
                      [ Thumb.LdrEq tmp1 heap;
                        Thumb.LdrEq tmp2 $ Thumb.Literal w;
                        Thumb.Add tmp1 tmp1 tmp2;
                        Thumb.Add tmp1 tmp1 $ regS r;
                        mnemonic reg tmp1 ]
  end.

Definition fetch (tmp : Thumb.register * Thumb.register)
                 (reg : Thumb.register)
                 (rvalue : IL.rvalue)
                 : list Thumb.instruction
                 :=
  let mem := memS tmp in
  match rvalue with
    | IL.RvLval lv => match lv with
                        | IL.LvReg r => [Thumb.Mov reg (regS r)]
                        | IL.LvMem loc => mem Thumb.Ldr reg loc
                        | IL.LvMem8 loc => mem Thumb.LdrB reg loc
                      end
    | IL.RvImm w => [Thumb.LdrEq reg $ Thumb.Literal w]
    | IL.RvLabel lab =>
      [Thumb.LdrEq reg $ Thumb.Label $ labelS lab]
  end.

Definition binop (op : IL.binop)
                 (dest : Thumb.register)
                 (left : Thumb.register)
                 (right : Thumb.register)
                 : Thumb.instruction
                 :=
  let mnemonic := match op with
                    | IL.Plus => Thumb.Add
                    | IL.Minus => Thumb.Sub
                    | IL.Times => Thumb.Mul
                  end
  in
  mnemonic dest left right.

Definition writeback (tmp : Thumb.register * Thumb.register)
                     (lvalue : IL.lvalue)
                     (reg : Thumb.register)
                     : list Thumb.instruction
                     :=
  let mem := memS tmp in
  match lvalue with
    | IL.LvReg r => [Thumb.Mov (regS r) reg]
    | IL.LvMem loc => mem Thumb.Str reg loc
    | IL.LvMem8 loc => mem Thumb.StrB reg loc
  end.

Definition cmpAndBranch (left : Thumb.register)
                        (op : IL.test)
                        (right : Thumb.register)
                        (ifTrue : label)
                        (ifFalse : label)
                      : list Thumb.instruction
                      :=
  (* Arm can't do a single-instruction compare to determine if x ≤ y.  Instead,
  we ask it to determine if ¬(y < x). *)
  let cond on := match op with
                   | IL.Eq => Thumb.EQ
                   | IL.Ne => Thumb.NE
                   | IL.Lt | IL.Le => Thumb.MI
                 end
  in
  (
    match op with
      | IL.Eq | IL.Ne | IL.Lt => Thumb.Cmp left right
      | IL.Le => Thumb.Cmp right left
    end
  ) :: (
    match op with
      | IL.Eq | IL.Ne | IL.Lt =>
        [ Thumb.CondBranch (cond op) $ labelS ifTrue;
          Thumb.Branch $ labelS ifFalse ]
      | IL.Le =>
        [ Thumb.CondBranch (cond op) $ labelS ifFalse;
          Thumb.Branch $ labelS ifTrue ]
    end
   ).

Definition instrS (instr : IL.instr) : list Thumb.instruction :=
  (* Reserve two temporary registers for the memory operations. *)
  let tmp := (Thumb.R5, Thumb.R6) in
  match instr with
    | IL.Assign lvalue rvalue =>
      (* On Intel, an assignment can be quite CISCy.  However, on a RISC ISA
      like Thumb, it's easiest to think of an assignment in two stages: a fetch
      and a writeback. *)
      fetch tmp Thumb.R3 rvalue ++ writeback tmp lvalue Thumb.R3
    | IL.Binop lvalue one op two =>
      (* Here, think about four stages: fetch the first rvalue, fetch the
      second rvalue, do the operation, and write back.  We'll use R3 and R4 to
      store the first and second rvalues, respectively, and we'll reuse R3 to
      store the result of the operation between the operation stage and the
      writeback. *)
      fetch tmp Thumb.R3 one
        ++ fetch tmp Thumb.R4 two
        ++ [binop op Thumb.R3 Thumb.R3 Thumb.R4]
        ++ writeback tmp lvalue Thumb.R3
  end.

Definition jmpS (j : IL.jmp) : list Thumb.instruction :=
  (* Reserve two temporary registers for the memory operations. *)
  let tmp := (Thumb.R5, Thumb.R6) in
  match j with
    | IL.Uncond target =>
      match target with
        | IL.RvLabel lab => [Thumb.Branch $ labelS lab]
        | rvalue => fetch tmp Thumb.R3 rvalue
                      ++ [ Thumb.Mov Thumb.PC Thumb.R3 ]
      end
    | IL.Cond one op two ifTrue ifFalse =>
      fetch tmp Thumb.R3 one
        ++ fetch tmp Thumb.R4 two
        ++ cmpAndBranch Thumb.R3 op Thumb.R4 ifTrue ifFalse
  end.

Definition blockS (b : IL.block) : list Thumb.instruction :=
  let (instructions, jump) := b in
  fold_right (fun instr text => instrS instr ++ text) (jmpS jump) instructions.

Local Close Scope list.  Local Open Scope string.

Definition moduleS (m : XCAP.module) : string :=
  let labeledBlockS (lab : label) (bl : XCAP.assert * IL.block) :=
      let (_, b) := bl in
      (
        match lab with
          | (_, Labels.Global functionName) =>
            ".globl " ++ labelS lab ++ Thumb.Show.newline
          | _ => ""
       end
      ) ++ labelS lab ++ ":" ++ Thumb.Show.newline
        ++ (concat $ map Thumb.Show.instruction $ blockS b)
  in
  (* A [LabelMap.t] is a proof-carrying data structure--it includes a proof
  that the tree underlying the map satisfies the invariants of an AVL tree.
  Since this part of the compiler is unverified, this proof is fairly useless,
  and it takes an extremely long time to compute.  Fortunately, it's not needed
  to produce a string of assembly code. *)
  LabelMap.fold (fun lab bl programText => labeledBlockS lab bl ++ programText)
                m.(XCAP.Blocks)
                "".

(* This declaration is _required_.  Without it, Coq can't compute the result of
[moduleS] far enough to actually yield a string of assembly. *)
Global Transparent natToWord.
