(** Definition of a simple intermediate language *)

Require Import List NArith String.

Require Import Word.


(** * Syntax *)

(* Machine registers 
 * There aren't many, since we'll use stack-allocated variables in most cases.
 * This is one of many decisions to trade off constant-factor performance for formalism simplicity in this early work. *)
Inductive reg :=
| Sp (* Stack pointer *)
| Rp (* Return pointer *)
| Rv (* Return value *).

(* Our machine words *)
Definition W := word 32.
Definition B := word 8.

(* Basic assignable locations *)
Inductive loc :=
| Reg : reg -> loc
| Imm : W -> loc
| Indir : reg -> W -> loc.

Coercion Reg : reg >-> loc.
Coercion Imm : W >-> loc.

(* Valid targets of assignments *)
Inductive lvalue :=
| LvReg : reg -> lvalue
| LvMem : loc -> lvalue.

Coercion LvReg : reg >-> lvalue.

(* Basic block labels *)
Inductive label' :=
| Global : string -> label'
| Local : N -> label'.

(* An overall label is a pair of a module name and a sub-label. *)
Definition label := prod string label'.

(* Operands *)
Inductive rvalue :=
| RvLval : lvalue -> rvalue
| RvImm : W -> rvalue
| RvLabel : label -> rvalue.

Coercion RvLval : lvalue >-> rvalue.
Coercion RvImm : W >-> rvalue.
Coercion RvLabel : label >-> rvalue.

(* Binary operations *)
Inductive binop := Plus | Minus | Times.

(* Non-control-flow instructions *)
Inductive instr :=
| Assign : lvalue -> rvalue -> instr
| Binop : lvalue -> rvalue -> binop -> rvalue -> instr.

(* Binary relational operators *)
Inductive test := Eq | Lt.

(* Jumps *)
Inductive jmp :=
| Uncond : rvalue -> jmp
| Cond : rvalue -> test -> rvalue -> label -> label -> jmp.

(* Basic blocks *)
Definition block := prod (list instr) jmp.


(** Semantics *)

(* Register banks *)
Definition regs := reg -> W.

Definition reg_eq : forall x y : reg, {x = y} + {x <> y}.
  decide equality.
Defined.

Definition rupd (rs : regs) (r : reg) (v : W) : regs := fun r' =>
  if reg_eq r' r then v else rs r'.

Theorem rupd_eq : forall rs r v, rupd rs r v r = v.
  intros; unfold rupd; destruct (reg_eq r r); tauto.
Qed.

Theorem rupd_ne : forall rs r v r', r' <> r -> rupd rs r v r' = rs r'.
  intros; unfold rupd; destruct (reg_eq r' r); tauto.
Qed.

Hint Rewrite rupd_eq rupd_ne using congruence : IL.

(* Memories *)
Definition mem := W -> B.

Open Scope word_scope.

Notation "$ n" := (natToWord _ n) (at level 0) : word_scope.

Definition separated (a1 a2 : W) :=
  forall n m, (n < 4)%nat -> (m < 4)%nat
    -> (a1 ^+ $ n) <> (a2 ^+ $ m).

Definition separatedB (a1 a2 : W) :=
  forall n, (n < 4)%nat
    -> a1 <> (a2 ^+ $ n).

(* Execution is parametric in settings that distinguish different platforms.
 * Programs will generally be verified to work in all platforms. *)
Record settings := {
  MemHigh : W;
  (* The first non-addressable RAM address *)
  WriteWord : mem -> W -> W -> mem;
  ReadWord : mem -> W -> W;
  (* Word-size memory access operations, which encode the endianness *)
  ReadWriteEq : forall m k v, ReadWord (WriteWord m k v) k = v;
  ReadWriteNe : forall m k v k', separated k' k
    -> ReadWord (WriteWord m k v) k' = ReadWord m k';
  ReadWriteNeB : forall m k v k', separatedB k' k
    -> WriteWord m k v k' = m k';
  (* Our only assumptions about the behavior of [WriteWord] and [ReadWord] *)
  Labels : label -> option W
  (* Locations of basic blocks *)
}.

Definition wring32 := wring 32.
Add Ring wring32 : wring32 (decidable (weqb_sound 32), constants [wcst]).

Theorem ReadWriteEq' : forall s m k v k', k' = k -> ReadWord s (WriteWord s m k v) k' = v.
  intros; subst; apply ReadWriteEq.
Qed.

Hint Rewrite ReadWriteEq' using (unfold W in *; word_eq) : IL.
Hint Rewrite ReadWriteNe using (unfold W in *; word_neq) : IL.

(* Machine states *)
Record state := {
  Regs : regs;
  Mem : mem
}.

Section settings.
  Variable stn : settings.

  (* Is a word-sized memory chunk in bounds, within addressable RAM? *)
  Definition inBounds (a : W) := a < MemHigh stn /\ a ^+ $3 < MemHigh stn.

  Definition inBounds_dec (a : W) : {inBounds a} + {~inBounds a}.
    refine (if wlt_dec a (MemHigh stn)
      then if wlt_dec (a ^+ $3) (MemHigh stn)
        then left _ _
        else right _ _
      else right _ _); abstract (unfold inBounds; tauto).
  Defined.

  Section state.
    Variable st : state.

    Definition evalLoc (l : loc) : option W :=
      match l with
        | Reg r => Some (Regs st r)
        | Imm w => Some w
        | Indir r w => let a := Regs st r ^+ w in
          if inBounds_dec a then Some a else None
      end.

    Definition evalLvalue (lv : lvalue) (v : W) : option state :=
      match lv with
        | LvReg r => Some {| Regs := rupd (Regs st) r v;
          Mem := Mem st |}
        | LvMem l => match evalLoc l with
                       | None => None
                       | Some a => if inBounds_dec a
                         then Some {| Regs := Regs st;
                           Mem := WriteWord stn (Mem st) a v |}
                         else None
                     end
      end.

    Definition evalRvalue (rv : rvalue) : option W :=
      match rv with
        | LvReg r => Some (Regs st r)
        | LvMem l => match evalLoc l with
                                | None => None
                                | Some a => if inBounds_dec a
                                  then Some (ReadWord stn (Mem st) a)
                                  else None
                              end
        | RvImm w => Some w
        | RvLabel l => Labels stn l
      end.

    Definition evalBinop (bo : binop) : W -> W -> W :=
      match bo with
        | Plus => @wplus _
        | Minus => @wminus _
        | Times => @wmult _
      end.

    Definition evalInstr (i : instr) : option state :=
      match i with
        | Assign lv rv => match evalRvalue rv with
                            | None => None
                            | Some w => evalLvalue lv w
                          end
        | Binop lv rv1 bo rv2 => match evalRvalue rv1, evalRvalue rv2 with
                                   | Some w1, Some w2 => evalLvalue lv (evalBinop bo w1 w2)
                                   | _, _ => None
                                 end
      end.

    Definition wltb (w1 w2 : W) : bool :=
      if wlt_dec w1 w2 then true else false.
    Definition weqb (w1 w2 : W) : bool :=
      if weq w1 w2 then true else false.

    Definition evalTest (ts : test) : W -> W -> bool :=
      match ts with
        | Lt => wltb
        | Eq => weqb
      end.

    Definition evalJmp (j : jmp) : option W :=
      match j with
        | Uncond rv => evalRvalue rv
        | Cond rv1 ts rv2 l1 l2 =>
          match evalRvalue rv1, evalRvalue rv2 with
            | Some w1, Some w2 => Labels stn (if evalTest ts w1 w2 then l1 else l2)
            | _, _ => None
          end
      end.
  End state.

  Fixpoint evalInstrs (st : state) (is : list instr) : option state :=
    match is with
      | nil => Some st
      | i :: is' => match evalInstr st i with
                      | None => None
                      | Some st' => evalInstrs st' is'
                    end
    end.

  (* States with program counters *)
  Definition state' := prod W state.

  Definition evalBlock (st : state) (b : block) : option state' :=
    let (is, j) := b in
      match evalInstrs st is with
        | None => None
        | Some st' => match evalJmp st' j with
                        | None => None
                        | Some w => Some (w, st')
                      end
      end.

  (* Program code *)
  Definition program := W -> option block.

  Variable prog : program.

  Definition step (st : state') : option state' :=
    match prog (fst st) with
      | None => None
      | Some b => evalBlock (snd st) b
    end.

  (* To define safety, we characterize reachability of states. *)
  Inductive reachable : state' -> state' -> Prop :=
  | Reachable0 : forall st, reachable st st
  | Reachable1 : forall st st' st'', step st = Some st'
    -> reachable st' st''
    -> reachable st st''.

  (* A state is safe if execution runs forever from it.*)
  Definition safe (st : state') := forall st', reachable st st'
    -> step st' <> None.
End settings.
