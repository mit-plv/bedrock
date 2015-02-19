(* Thumb2_gas -- Thumb-2 code generator *)

(** printing ++ $+\kern-0.3em+$ *)

(** This module, like [I386_gas] and [AMD64_gas] before it, generates ARM
Thumb-2 code from the Bedrock IL.  Unlike those generators, however,
[Thumb2_gas] generates code in two steps.  In the first, it converts the
Bedrock IL (an abstract CISC ISA) to an embedded subset of ARM assembly (a RISC
ISA); in the second, it serializes the embedded ARM assembly to a [string]
suitable for GAS consumption. *)

Require Import List.  Import ListNotations.

Require Import FastString.


(** A function application operator, à la Haskell, makes quite a bit of the
code below much more readable. *)

Notation "f $ x" := (f x) (at level 100, right associativity, only parsing).


(** * Partial Thumb-2 machine definition

We support only a subset of the Thumb-2 ISA.  Should other opcodes become
useful at a later date, it will be easy to add them. *)

Module Thumb.
  Require Import Ascii.

  Require Import Memory.
  Require Import Word.

  Local Open Scope nat.
  Local Open Scope string.
  Set Implicit Arguments.

  (** Thumb-2 supports the first eight general-purpose registers (R0–R7), the
  condition flag register, and the program counter.  We don’t need all of the
  registers, however. *)

  Inductive register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | PC.

  Inductive litOrLabel :=
  | Literal : W -> litOrLabel
  | Label : string -> litOrLabel.

  (** Thumb-2 supports a whole host of condition flags, but these three are
  sufficient to implement Bedrock’s conditional jumps. *)

  Inductive condition := EQ | NE | MI.

  (** We need very few Thumb mnemonics to actually compile Bedrock code:
  <<mov>> and <<ldr =>>, four load and store instrucitons, three arithmetic
  operations, and three branching opcodes.  Note that <<ldr =>> (e.g., <<ldr
  r1, =12345>>) is not an actual Thumb mnemonic but rather a GAS-provided
  pseudo-opcode that cleverly skirts Thumb’s limitations on immediates in
  <<mov>> instructions.  See
  <<https://sourceware.org/binutils/docs/as/ARM-Opcodes.html#index-g_t_0040code_007bLDR-reg_002c_003d_003clabel_003e_007d-pseudo-op_002c-ARM-700>> for
  a more complete rundown. *)

  Inductive instruction :=
  | Mov : register -> register -> instruction
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


  (** ** Serializing to [string] *)

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


(** * Converting [IL.instr] to [Thumb.instruction] *)

Require IL.
Require Import LabelMap.
Require Import Labels.
Require Import Memory.
Require Import Word.
Require XCAP.

(** Make [natToWord] transparent so Coq can actually compute the result of
[moduleS] far enough to actually yield a string of assembly. *)

Global Transparent natToWord.


(** ** Atoms

Words, registers, and labels are very easy to convert. *)

Local Open Scope string.

Fixpoint wordS {sz} (w : word sz) : string :=
  match w with
    | WO => ""
    | WS false _ w' => wordS w' ++ "0"
    | WS true _ w' => wordS w' ++ "1"
  end.

Definition binS {sz} (w : word sz) : string :=
  "0b" ++ wordS w.

(** The Bedrock IL requires only three registers.  We map them to the first
three ARM registers, leaving R3–R7 available for scratchpad use. *)

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

Local Close Scope string.


(** ** Memory operations

Here’s where things start to get complicated.  Thumb’s chief limitation is
memory addressing – it supports a 32-bit address bus, but instructions may only
be 16 bits wide.  Thus, many memory-related [IL.instr]s (e.g., memory-to-memory
assignments) become multiple Thumb instructions. *)

Local Open Scope list.

(** [memS] applies [mnemonic] to the register [reg] and the memory location
described by [loc] to execute a load or a store.  It uses [tmp1] and [tmp2] as
scratchpad registers; each must be different from [reg] (and the other).  _This
precondition is currently unchecked_.

Handling memory operations with offsets is slightly painful.  Thumb’s memory
operations do support offsets baked into the instructions, but they have a hard
width limit.  For simplicity, we assume the offsets are too large and just put
them in registers.  *)

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
    | IL.Imm w => [ Thumb.LdrEq tmp1 heap;
                    Thumb.LdrEq tmp2 $ Thumb.Literal w;
                    Thumb.Add tmp1 tmp1 tmp2;
                    mnemonic reg tmp1 ]
    | IL.Indir r w => [ Thumb.LdrEq tmp1 heap;
                        Thumb.LdrEq tmp2 $ Thumb.Literal w;
                        Thumb.Add tmp1 tmp1 tmp2;
                        Thumb.Add tmp1 tmp1 $ regS r;
                        mnemonic reg tmp1 ]
  end.

(** Fetches [rvalue] from memory and stores it in [reg]. *)

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

(** Stores the value of [reg] in memory at [lvalue]. *)

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


(** ** Arithmetic

Compared with memory operations, arithmetic is trivial. *)

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


(** ** Branches

Branches are also fairly easy – a <<cmp>> instruction followed by a couple
of <<b>>s.  Thumb doesn’t have a single-instruction compare to determine if
$x < y$#x ≤  y#, so instead, we use the equivalent check
$\lnot(y < x)$#¬(y < x)#. *)

Definition cmpAndBranch (left : Thumb.register)
                        (op : IL.test)
                        (right : Thumb.register)
                        (ifTrue : label)
                        (ifFalse : label)
                      : list Thumb.instruction
                      :=
  let cond op := match op with
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


(** ** Instructions and blocks *)

(** On Intel, an assignment can be quite CISCy.  However, on a RISC ISA like
Thumb, it’s easiest to think of an assignment in two stages: a fetch and a
writeback.

For a binary operation, think about four stages: fetch the first rvalue, fetch
the second rvalue, do the operation, and write back.  We’ll use R3 and R4 to
store the first and second rvalues, respectively, and we’ll reuse R3 to store
the result of the operation between the operation stage and the writeback. *)

Definition instrS (instr : IL.instr) : list Thumb.instruction :=
  let tmp := (Thumb.R5, Thumb.R6) in
  match instr with
    | IL.Assign lvalue rvalue =>
    fetch tmp Thumb.R3 rvalue ++ writeback tmp lvalue Thumb.R3
    | IL.Binop lvalue one op two =>
      fetch tmp Thumb.R3 one
        ++ fetch tmp Thumb.R4 two
        ++ [binop op Thumb.R3 Thumb.R3 Thumb.R4]
        ++ writeback tmp lvalue Thumb.R3
  end.

Definition jmpS (j : IL.jmp) : list Thumb.instruction :=
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

Local Close Scope list.


(** ** Final serialization *)

Local Open Scope string.

(** [moduleS] presents the public interface for the assembler.  It extracts the
[LabelMap.t] from an [XCAP.module] and folds over it to produce a string.

Formerly, [moduleS] produced a [LabelMap.t] mapping labels to strings of
assembly.  However, a [LabelMap.t] is a proof-carrying data structure – it
includes a proof that the tree underlying the map satisfies the invariants of
an AVL tree.  Since this part of the compiler is unverified, this proof is
fairly useless, and it takes an extremely long time to compute.  By having
[moduleS] produce a [string], the compiler thus gains a substantial performance
boost. *)

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
  LabelMap.fold (fun lab bl programText => labeledBlockS lab bl ++ programText)
                m.(XCAP.Blocks)
                "".
