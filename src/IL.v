(** Definition of a simple intermediate language *)

Require Import Arith Div2 List NArith String.

Require Import Nomega Word Memory.


(* Our machine words *)
Definition W := word 32.
Definition B := word 8.

(** * Setting up hidden word constants *)

Fixpoint natToWord' (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord' sz' (div2 n))
  end.

Definition natToW (n : nat) : W := natToWord _ n.

Definition isConst (n : nat) := True.

Theorem natToWord_expose : forall n w, isConst w -> natToWord n w = natToWord' n w.
  reflexivity.
Qed.

Theorem natToW_expose : forall n, isConst n -> natToW n = natToWord' _ n.
  reflexivity.
Qed.

Ltac isConst :=
  let rec f n :=
    match n with
      | O => idtac
      | S ?n' => f n'
    end in
    match goal with
      [ |- isConst ?n ] => f n; constructor
    end.


(** * Syntax *)

(* Machine registers 
 * There aren't many, since we'll use stack-allocated variables in most cases.
 * This is one of many decisions to trade off constant-factor performance for formalism simplicity in this early work. *)
Inductive reg :=
| Sp (* Stack pointer *)
| Rp (* Return pointer *)
| Rv (* Return value *).

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
Inductive test := Eq | Ne | Lt | Le.

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

(** * A useful principle for separated *)

Ltac wprepare := repeat match goal with
                          | [ |- context[natToWord ?n ?m] ] => rewrite (natToWord_expose n m) by isConst
                          | [ |- context[natToW ?n] ] => rewrite (natToW_expose n) by isConst
                        end; unfold W in *.

Definition wring32 := wring 32.
Add Ring wring32 : wring32 (decidable (weqb_sound 32), constants [wcst]).

Definition Wring : @ring_theory W _ _ _ _ _ _ _ := wring 32.
Add Ring Wring : Wring (decidable (weqb_sound 32), constants [wcst]).

Lemma cancel : forall u v k : W,
  u ^+ k = v ^+ k
  -> u = v.
  intros.
  apply (f_equal (fun x => x ^+ ^~ k)) in H.
  replace (u ^+ k ^+ ^~ k) with u in H by (wprepare; word_eq).
  replace (v ^+ k ^+ ^~ k) with v in H by (wprepare; word_eq).
  auto.
Qed.

Hint Immediate cancel.

Lemma cancel_contra : forall u v k : W,
  u <> v
  -> u ^+ k <> v ^+ k.
  generalize cancel; firstorder.
Qed.

Hint Immediate cancel_contra.

Lemma natToWordToN : forall n m, (N_of_nat m < Npow2 n)%N
  -> wordToN (natToWord n m) = N_of_nat m.
  intros.
  rewrite wordToN_nat.
  destruct (wordToNat_natToWord n m); intuition.
  rewrite H1; clear H1.
  destruct x.
  nomega.
  elimtype False.
  simpl in *.
  generalize dependent (x * pow2 n).
  rewrite <- Npow2_nat in *.
  intros.
  nomega.
Qed.

Lemma cancel_contra_minus : forall k1 k2 (u v : W),
  u ^+ $ k1 = v ^+ $ k2
  -> (k1 < k2)%nat
  -> (N_of_nat k2 < Npow2 32)%N
  -> u = v ^+ $ (k2 - k1).
  intros.
  apply cancel with ($ k1).
  rewrite H; clear H.
  rewrite <- wplus_assoc.
  f_equal.
  unfold wplus, wordBin.
  repeat rewrite natToWordToN.
  rewrite <- N_of_plus.
  replace (k2 - k1 + k1) with k2 by omega.
  rewrite NToWord_nat.
  autorewrite with N; reflexivity.
  auto.
  generalize dependent (Npow2 32).
  intros.
  nomega.
  generalize dependent (Npow2 32).
  intros.
  nomega.
Qed.

Lemma cancel_contra_minus' : forall k1 k2 (u v : W),
  u <> v ^+ $ (k2 - k1)%nat
  -> (k1 < k2)%nat
  -> (N_of_nat k2 < Npow2 32)%N
  -> u ^+ $ k1 <> v ^+ $ k2.
  intros; intro.
  apply H.
  eapply cancel_contra_minus; eauto.
Qed.

Lemma cancel_contra_minus'' : forall k1 k2 (u v : W),
  v ^+ $ (k2 - k1)%nat <> u
  -> (k1 < k2)%nat
  -> (N_of_nat k2 < Npow2 32)%N
  -> v ^+ $ k2 <> u ^+ $ k1.
  intros; intro.
  apply H.
  symmetry.
  eapply cancel_contra_minus; eauto.
Qed.

Local Hint Extern 1 (_ <> _) => apply cancel_contra_minus'; [ assumption | omega | reflexivity ].
Local Hint Extern 1 (_ <> _) => apply cancel_contra_minus''; [ assumption | omega | reflexivity ].

Theorem const_separated : forall u v,
  u <> v
  -> u <> v ^+ $ 1
  -> u <> v ^+ $ 2
  -> u <> v ^+ $ 3
  -> u ^+ $ 1 <> v
  -> u ^+ $ 2 <> v
  -> u ^+ $ 3 <> v
  -> separated u v.
  red; intros.
  repeat match goal with
           | [ H : (_ < _)%nat |- _ ] => inversion H; clear H; subst
           | [ H : (_ <= _)%nat |- _ ] => inversion H; clear H; subst
         end; auto.
Qed.


(** * Settings *)

(* Execution is parametric in settings that distinguish different platforms.
 * Programs will generally be verified to work in all platforms. *)
Record settings := {
  MemHigh : W;
  (* The first non-addressable RAM address *)
  implode : B * B * B * B -> W ;
  explode : W -> B * B * B * B ;
  (* conversion for reading words *)

  implode_explode : forall w,
    implode (explode w) = w ;
  explode_implode : forall b,
    explode (implode b) = b ;

  Labels : label -> option W
  (* Locations of basic blocks *)
}.

Definition ReadByte (_ : settings) (m : mem) (a : W) : B :=
  m a.

Definition ReadWord (s : settings) (m : mem) (a : W) : W :=
  let v1 := m a in
  let v2 := m (a ^+ $1) in
  let v3 := m (a ^+ $2) in
  let v4 := m (a ^+ $3) in
  implode s (v1, v2, v3, v4).

Definition WriteByte (_ : settings) (m : mem) (p : W) (v : B) : mem :=
  fun p' => if weq p' p then v else m p'.

Definition WriteWord (s : settings) (m : mem) (p v : W) : mem :=
  let '(v1,v2,v3,v4) := explode s v in
  fun p' =>
    if weq p' p then v1 
    else if weq p' (p ^+ $1) then v2
         else if weq p' (p ^+ $2) then v3
              else if weq p' (p ^+ $3) then v4
                   else m p'.

Ltac W_eq := wprepare; word_eq.
Ltac W_neq := (apply const_separated; word_neq) || (wprepare; word_neq).

Theorem ReadWriteEq : forall stn m k v, ReadWord stn (WriteWord stn m k v) k = v.
Proof.
  unfold ReadWord, WriteWord. intros.
  case_eq (explode stn v). destruct p. destruct p.
  repeat rewrite (rewrite_weq (refl_equal _)).
  repeat match goal with
           | [ |- context [ weq ?X ?Y ] ] => 
             let Z := fresh in destruct (weq X Y) as [ Z | ? ]; [ exfalso; generalize Z; W_neq | ]
         end.
  intros. rewrite <- H. apply implode_explode.
Qed.

Theorem ReadWriteNe : forall stn m k v k', separated k' k
  -> ReadWord stn (WriteWord stn m k v) k' = ReadWord stn m k'.
Proof.
  unfold ReadWord, WriteWord; intros.
  case_eq (explode stn v); intros. destruct p. destruct p.
  assert (k' = k' ^+ $(0)). W_eq.
  assert (k = k ^+ $(0)). W_eq.
  repeat match goal with
    | [ |- context [ weq ?X ?Y ] ] => 
      let Z := fresh in destruct (weq X Y) as [ Z | ? ]; 
        [ exfalso ; (apply H in Z || (rewrite H1 in Z; apply H in Z) || (rewrite H2 in Z; apply H in Z) || (rewrite H1 in Z; rewrite H2 in Z; apply H in Z)); auto; omega |  ]  
  end.
  reflexivity.
Qed.  

Theorem ReadWordFootprint : forall stn m m' a a',
  m a = m' a'
  -> m (a ^+ $1) = m' (a' ^+ $1)
  -> m (a ^+ $2) = m' (a' ^+ $2)
  -> m (a ^+ $3) = m' (a' ^+ $3)
  -> ReadWord stn m a = ReadWord stn m' a'.
Proof.
  unfold ReadWord. intros. congruence.
Qed. 

Theorem ReadWriteEq' : forall s m k v k', k' = k -> ReadWord s (WriteWord s m k v) k' = v.
  intros; subst; apply ReadWriteEq.
Qed.

Hint Rewrite ReadWriteEq' using W_eq : IL.
Hint Rewrite ReadWriteNe using solve [ auto ] : IL.

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
                       | Some a =>
                         if inBounds_dec a
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
                       | Some a =>
                         if inBounds_dec a
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
    Definition wneb (w1 w2 : W) : bool :=
      if weq w1 w2 then false else true.
    Definition wleb (w1 w2 : W) : bool :=
      if weq w1 w2 then true else if wlt_dec w1 w2 then true else false.

    Definition evalTest (ts : test) : W -> W -> bool :=
      match ts with
        | Lt => wltb
        | Eq => weqb
        | Ne => wneb
        | Le => wleb
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
