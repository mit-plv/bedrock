Require Import PreAutoSep Wrap Conditional.

Import DefineStructured.

Set Implicit Arguments.


(** Simple notation for parsing streams of machine words *)

Inductive pattern0 :=
| Const_ (_ : W)
(* Match this exact word. *)
| Var_ (_ : string)
(* Match anything and stash it in this local variable. *).

Definition pattern := list pattern0.
(* Match a prefix of the stream against these individual word patterns. *)

Definition Const w : pattern := Const_ w :: nil.
Definition Var x : pattern := Var_ x :: nil.

Coercion Const : W >-> pattern.
Coercion Var : string >-> pattern.

Fixpoint matches (p : pattern) (ws ws' : list W) : Prop :=
  match p, ws with
    | nil, _ => ws' = ws
    | Const_ w :: p', w' :: ws'' => w = w' /\ matches p' ws'' ws'
    | Var_ _ :: p', _ :: ws'' => matches p' ws'' ws'
    | _, _ => False
  end.

Fixpoint binds (p : pattern) (ws : list W) : list (string * W) :=
  match p, ws with
    | Const_ _ :: p', _ :: ws' => binds p' ws'
    | Var_ s :: p', w :: ws' => (s, w) :: binds p' ws'
    | _, _ => nil
  end.

Section Parse.
  Variable stream : string.
  (* Name of local variable containing an array to treat as the stream of words *)
  Variable size : string.
  (* Name of local variable containing the stream length in words *)
  Variable pos : string.
  (* Name of local variable containing the current stream position in words *)

  Variable p : pattern.
  (* We will try to match a prefix of the stream against this pattern. *)

  Variable imports : LabelMap.t assert.
  Hypothesis H : importsGlobal imports.
  Variable modName : string.

  Variables Then Else : cmd imports modName.
  (* Code to run when a single pattern matches or fails, respectively. *)

  Variable ns : list string.
  (* Local variable names *)

  (* Does the pattern match? *)
  Fixpoint guard (p : pattern) (offset : nat) : bexp :=
    match p with
      | nil =>
        Test Rv Le (variableSlot size ns)
        (* Is there enough space left in the stream? *)
      | Const_ w :: p' =>
        And (guard p' (S offset))
        (Test (LvMem (Indir Rp (4 * offset))) IL.Eq w)
      | Var_ _ :: p' => guard p' (S offset)
    end.

  (* Once we know that the pattern matches, we set the appropriate pattern variables with this function. *)
  Fixpoint reads (p : pattern) (offset : nat) : list instr :=
    match p with
      | nil => nil
      | Const_ _ :: p' => reads p' (S offset)
      | Var_ x :: p' => Assign (variableSlot x ns) (LvMem (Indir Rp offset)) :: reads p' (S offset)
    end.

  (* Here's the raw parsing command, which we will later wrap with nicer VCs/postcondition. *)
  Definition Parse1_ : cmd imports modName :=
    Seq_ H (Straightline_ _ _ (Binop Rv (variableSlot pos ns) Plus (length p)
      :: Binop Rp 4 Times (variableSlot pos ns)
      :: Binop Rp (variableSlot stream ns) Plus Rp
      :: nil))
    (Cond_ _ H _ (guard p O)
      (Straightline_ _ _ (reads p O
        ++ Binop (variableSlot pos ns) (variableSlot pos ns) Plus (length p)
        :: nil))
      Else).

  Opaque mult evalRvalue.

  Theorem guard_bound : forall stn st p offset, bexpTrue (guard p offset) stn st
    -> exists sizeV, evalRvalue stn st (variableSlot size ns) = Some sizeV
      /\ Regs st Rv <= sizeV.
    induction p0 as [ | [ ] ]; simpl; intros; eauto.

    unfold evalCond in H0; simpl in H0.
    Transparent evalRvalue.
    unfold evalRvalue in H0 at 1.
    destruct (evalRvalue stn st (variableSlot size ns)); try (intuition discriminate).
    injection H0; clear H0; intros.
    unfold wleb in H0.
    destruct (weq (Regs st Rv) w); subst.
    eauto.
    destruct (wlt_dec (Regs st Rv) w); eauto; discriminate.

    firstorder.
  Qed.

  Fixpoint suffix (n : nat) (ws : list W) : list W :=
    match n with
      | O => ws
      | S n' => match ws with
                  | nil => nil
                  | w :: ws' => suffix n' ws'
                end
    end.

  Lemma suffix_remains : forall n ws,
    (n < length ws)%nat
    -> suffix n ws = selN ws n :: suffix (S n) ws.
    induction n; destruct ws; simpl; intuition.
    rewrite IHn; auto.
  Qed.

  Hint Rewrite wordToN_nat wordToNat_natToWord_idempotent using assumption : N.
  Require Import Arith.

  Theorem lt_goodSize : forall n m,
    (n < m)%nat
    -> goodSize n
    -> goodSize m
    -> natToW n < natToW m.
    unfold goodSize, natToW, W; generalize 32; intros; nomega.
  Qed.

  Theorem goodSize_weaken : forall n m,
    goodSize n
    -> (n >= m)%nat
    -> goodSize m.
    unfold goodSize; generalize 32; intros; nomega.
  Qed.

  Hint Resolve lt_goodSize goodSize_weaken.

  Hint Extern 1 (_ >= _)%nat => omega.

  Theorem wle_goodSize : forall n m,
    natToW n <= natToW m
    -> goodSize n
    -> goodSize m
    -> (n <= m)%nat.
    intros.
    destruct (le_lt_dec n m); auto.
    elimtype False.
    apply H0.
    apply Nlt_in.
    autorewrite with N.
    auto.
  Qed.

  Theorem guard_matches : forall stn st specs ptr ws fr posV,
    evalRvalue stn st (variableSlot stream ns) = Some ptr
    -> interp specs (![array ws ptr * fr] (stn, st))
    -> evalRvalue stn st (variableSlot size ns) = Some $(length ws)
    -> evalRvalue stn st (variableSlot pos ns) = Some $(posV)
    -> Regs st Rp = ptr ^+ $(4 * posV)
    -> forall p' offset, bexpTrue (guard p' offset) stn st
      -> Regs st Rv = $(posV + offset + length p')
      -> goodSize (posV + offset + length p')
      -> exists ws', matches p' (suffix (offset + posV) ws) ws'.
    induction p' as [ | [ ] ]; simpl; intuition eauto.

    assert (goodSize (length ws)) by eauto.
    destruct (IHp' _ H8); clear IHp'; auto.
    rewrite H6; repeat (omega || f_equal).
    eauto.
    apply guard_bound in H8; destruct H8 as [ ? [ ] ].
    rewrite H2 in H8; injection H8; clear H8; intros; subst.
    rewrite H6 in H11.
    apply wle_goodSize in H11; eauto.
    rewrite suffix_remains by omega.
    repeat esplit; eauto.
    generalize H1 H4 H7 H9 H11; clear; intros.
    assert (evalCond (LvMem (Imm (ptr ^+ $4 ^* $(offset + posV)))) IL.Eq w stn st = Some true).
    unfold evalCond in *.
    simpl in *.
    rewrite H4 in H9.
    match goal with
      | [ _ : context[ReadWord _ _ ?A] |- context[ReadWord _ _ ?B] ] => replace B with A
    end; auto.
    rewrite mult_comm; rewrite natToW_times4.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    W_eq.
    clear H9.
    assert ($(offset + posV) < natToW (length ws)) by eauto.
    evaluate auto_ext.
    subst.
    unfold Array.sel.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize (offset + posV)).
    rewrite plus_comm; eauto.

    destruct (IHp' _ H5).
    rewrite H6; repeat (omega || f_equal).
    eauto.
    apply guard_bound in H5; destruct H5 as [ ? [ ] ].
    rewrite H2 in H5; injection H5; clear H5; intros; subst.
    rewrite H6 in H9.
    apply wle_goodSize in H9; eauto.
    rewrite suffix_remains by omega.
    eauto.
  Qed.

  Opaque evalRvalue.

  Fixpoint okVarName (x : string) (p : pattern) : Prop :=
    match p with
      | nil => True
      | Const_ _ :: p' => okVarName x p'
      | Var_ x' :: p' => if string_dec x x' then False else okVarName x p'
    end.

  Transparent evalInstrs.

  Lemma evalInstrs_app_fwd : forall stn is2 st' is1 st,
    evalInstrs stn st (is1 ++ is2) = Some st'
    -> exists st'', evalInstrs stn st is1 = Some st''
      /\ evalInstrs stn st'' is2 = Some st'.
    induction is1; simpl; intuition eauto.
    destruct (evalInstr stn st a); eauto; discriminate.
  Qed.

  Transparent evalRvalue.

  Lemma variablePosition_different : forall x y, x <> y
    -> forall ns', In x ns'
      -> In y ns'
      -> variablePosition ns' x <> variablePosition ns' y.
    induction ns'; simpl; intuition; subst;
      repeat match goal with
               | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; subst; intuition
             end.
  Qed.

  Lemma variablePosition_bound : forall x ns', In x ns'
    -> (variablePosition ns' x < 4 * length ns')%nat.
    induction ns'; simpl; intuition; subst;
      repeat match goal with
               | [ |- context[if ?E then _ else _] ] => destruct E; subst; intuition
             end.
  Qed.

  Hint Rewrite N2Nat.inj_mul : N.

  Lemma variablePosition_separated : forall x y ns', x <> y
    -> In x ns'
    -> In y ns'
    -> (N_of_nat (length ns') < Npow2 30)%N
    -> separated (variablePosition ns' x) (variablePosition ns' y).
    intros.
    hnf; intros.
    specialize (variablePosition_different H0 _ H1 H2); intro Hdiff.
    specialize (variablePosition_bound _ _ H1); intro Hx.
    specialize (variablePosition_bound _ _ H2); intro Hy.
    autorewrite with sepFormula.
    rewrite <- (variablePosition'_4 x ns') in *.
    rewrite <- (variablePosition'_4 y ns') in *.
    assert (variablePosition' ns' x * 4 + n <> variablePosition' ns' y * 4 + m) by omega.
    intro; apply H6.
    apply natToW_inj; auto.

    red.
    assert (Npow2 32 = 4 * Npow2 30)%N by reflexivity.
    generalize dependent (Npow2 30).
    generalize dependent (Npow2 32); intros.
    subst.
    rewrite Nmult_comm.
    nomega.

    red.
    assert (Npow2 32 = 4 * Npow2 30)%N by reflexivity.
    generalize dependent (Npow2 30).
    generalize dependent (Npow2 32); intros.
    subst.
    rewrite Nmult_comm.
    nomega.
  Qed.

  Theorem separated_add : forall w1 w2,
    separated w1 w2
    -> forall w, separated (w ^+ w1) (w ^+ w2).
    unfold separated; intros.
    specialize (H0 _ _ H1 H2).
    intro; apply H0.
    do 2 rewrite <- wplus_assoc in H3.
    apply (f_equal (fun w' => ^~ w ^+ w')) in H3.
    repeat rewrite (wplus_assoc (^~ w)) in H3.
    repeat rewrite (wplus_comm (^~ w)) in H3.
    repeat rewrite wminus_inv in H3.
    repeat rewrite wplus_unit in H3; assumption.
  Qed.

  Hint Resolve separated_add.

  Fixpoint patternBound (p : pattern) : Prop :=
    match p with
      | nil => True
      | Const_ _ :: p' => patternBound p'
      | Var_ x :: p' => In x ns /\ patternBound p'
    end.

  Lemma stack_write_leaves_alone : forall stn st x rv st' y,
    evalInstr stn st (Assign (variableSlot x ns) rv) = Some st'
    -> y <> x
    -> In x ns
    -> In y ns
    -> (N_of_nat (length ns) < Npow2 30)%N
    -> evalRvalue stn st' (variableSlot y ns) = evalRvalue stn st (variableSlot y ns).
    simpl; unfold evalRvalue; intros.
    destruct (match rv with
                | RvLval (LvReg r) => Some (Regs st r)
                | RvLval (LvMem l) => ReadWord stn (Mem st) (evalLoc st l)
                | RvImm w => Some w
                | RvLabel l => Labels stn l
              end); try discriminate.
    case_eq (WriteWord stn (Mem st)
      (Regs st Sp ^+ natToW (S (S (S (S (variablePosition ns x)))))) w); intros;
    match goal with
      | [ H : _ = _ |- _ ] => rewrite H in *
    end; try discriminate.
    injection H0; clear H0; intros; subst; simpl.
    eapply ReadWriteNe in H5.
    apply H5.
    specialize (variablePosition_separated _ H1 H3 H2 H4); intro.
    repeat match goal with
             | [ |- context[S ?N] ] => rewrite (natToW_S N)
           end.
    eauto 6.
  Qed.

  Lemma stack_binop_leaves_alone : forall stn st x rv1 op rv2 st' y,
    evalInstr stn st (Binop (variableSlot x ns) rv1 op rv2) = Some st'
    -> y <> x
    -> In x ns
    -> In y ns
    -> (N_of_nat (length ns) < Npow2 30)%N
    -> evalRvalue stn st' (variableSlot y ns) = evalRvalue stn st (variableSlot y ns).
    simpl; unfold evalRvalue; intros.
    destruct (match rv1 with
                | RvLval (LvReg r) => Some (Regs st r)
                | RvLval (LvMem l) => ReadWord stn (Mem st) (evalLoc st l)
                | RvImm w => Some w
                | RvLabel l => Labels stn l
              end); try discriminate.
    destruct (match rv2 with
                | RvLval (LvReg r) => Some (Regs st r)
                | RvLval (LvMem l) => ReadWord stn (Mem st) (evalLoc st l)
                | RvImm w => Some w
                | RvLabel l => Labels stn l
              end); try discriminate.
    case_eq (WriteWord stn (Mem st)
      (Regs st Sp ^+ natToW (S (S (S (S (variablePosition ns x)))))) (evalBinop op w w0)); intros;
    match goal with
      | [ H : _ = _ |- _ ] => rewrite H in *
    end; try discriminate.
    injection H0; clear H0; intros; subst; simpl.
    eapply ReadWriteNe in H5.
    apply H5.
    specialize (variablePosition_separated _ H1 H3 H2 H4); intro.
    repeat match goal with
             | [ |- context[S ?N] ] => rewrite (natToW_S N)
           end.
    eauto 6.
  Qed.

  Opaque evalRvalue evalInstr.

  Theorem reads_leave_alone : forall stn st' p' offset st x,
    evalInstrs stn st (reads p' offset) = Some st'
    -> okVarName x p'
    -> In x ns
    -> patternBound p'
    -> (N.of_nat (Datatypes.length ns) < Npow2 30)%N
    -> evalRvalue stn st' (variableSlot x ns) = evalRvalue stn st (variableSlot x ns).
    induction p' as [ | [ ] ]; simpl; intuition eauto.
    congruence.
    case_eq (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + offset)%loc))); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end; try discriminate.
    destruct (string_dec x s); try tauto.
    eapply IHp' in H0; clear IHp'; try apply H1; auto.
    rewrite H0.
    eapply stack_write_leaves_alone; eauto.
  Qed.

  Theorem reads_leave_alone' : forall stn st' p' offset st x,
    evalInstrs stn st (reads p' offset
      ++ Binop (variableSlot pos ns) (variableSlot pos ns) Plus (length p)
      :: nil) = Some st'
    -> okVarName x p'
    -> In x ns
    -> patternBound p'
    -> x <> pos
    -> In pos ns
    -> (N.of_nat (Datatypes.length ns) < Npow2 30)%N
    -> evalRvalue stn st' (variableSlot x ns) = evalRvalue stn st (variableSlot x ns).
    intros.
    apply evalInstrs_app_fwd in H0; destruct H0 as [ ? [ ] ].
    erewrite <- (@reads_leave_alone _ _ _ _ st); try apply H0; auto.
    Transparent evalInstrs.
    simpl in H7.
    Opaque evalInstrs.
    case_eq (evalInstr stn x0 (Binop (variableSlot pos ns) (variableSlot pos ns)
      Plus (Datatypes.length p))); intros;
    match goal with
      | [ H : _ = _ |- _ ] => rewrite H in *
    end; try discriminate.
    injection H7; clear H7; intros; subst.
    eapply stack_binop_leaves_alone; eauto.
  Qed.

  Theorem reads_increment : forall stn st' p' offset st posV,
    evalInstrs stn st (reads p' offset
      ++ Binop (variableSlot pos ns) (variableSlot pos ns) Plus (length p')
      :: nil) = Some st'
    -> patternBound p'
    -> In pos ns
    -> okVarName pos p'
    -> (N.of_nat (Datatypes.length ns) < Npow2 30)%N
    -> evalRvalue stn st (variableSlot pos ns) = Some posV
    -> evalRvalue stn st' (variableSlot pos ns) = Some (posV ^+ $(length p')).
    intros.
    apply evalInstrs_app_fwd in H0; destruct H0 as [ ? [ ] ].
    erewrite <- (@reads_leave_alone _ _ _ _ st) in H5; try apply H0; auto.
    Transparent evalInstrs evalInstr.
    simpl in H6.
    Opaque evalInstrs evalInstr.
    Transparent evalRvalue.
    unfold evalRvalue in H6 at 2.
    Opaque evalRvalue.
    rewrite H5 in H6.
    match type of H6 with
      | match match ?E with None => _ | _ => _ end with None => _ | _ => _ end = _ => case_eq E
    end; intros;
    match goal with
      | [ H : _ = _ |- _ ] => rewrite H in *
    end; try discriminate.
    injection H6; clear H6; intros; subst.
    Transparent evalRvalue.
    simpl in *.
    eapply ReadWriteEq.
    eauto.
    Opaque evalRvalue.
  Qed.

  Definition Parse1 : cmd imports modName.
    refine (Wrap _ H _ Parse1_
      (fun pre stn_st => let (stn, st) := stn_st in
        Ex st', pre (stn, st')
        /\ Ex ptr, [| evalRvalue stn st' (variableSlot stream ns) = Some ptr
          /\ evalRvalue stn st (variableSlot stream ns) = Some ptr |]
        /\ Ex ws, [| evalRvalue stn st' (variableSlot size ns) = Some $(length ws)
          /\ evalRvalue stn st (variableSlot size ns) = Some $(length ws) |]
        /\ Ex posV, [| evalRvalue stn st' (variableSlot pos ns) = Some $(posV)
          /\ (posV <= length ws)%nat
          /\ evalRvalue stn st (variableSlot pos ns) = Some $(posV + length p) |]
        /\ (ExX, ![ ^[array ws ptr] * #0 ] (stn, st'))
        /\ ((Ex ws', [| matches p (suffix posV ws) ws' |])
          \/ (Al ws', [| ~matches p (suffix posV ws) ws' |])))%PropX
      (fun pre =>
        (N_of_nat (length ns) < Npow2 30)%N
        :: In stream ns
        :: In size ns
        :: In pos ns
        :: patternBound p
        :: okVarName stream p
        :: okVarName size p
        :: okVarName pos p
        :: NoDup (stream :: size :: pos :: nil)
        :: (forall stn st specs,
          interp specs (pre (stn, st))
          -> interp specs (Ex ptr, [| evalRvalue stn st (variableSlot stream ns) = Some ptr |]
            /\ Ex ws, [| evalRvalue stn st (variableSlot size ns) = Some $(length ws)
              /\ goodSize (length ws + length p)
              /\ exists posV, evalRvalue stn st (variableSlot pos ns) = Some $(posV)
                /\ (posV <= length ws)%nat |]
            /\ ExX, ![ ^[array ws ptr] * #0 ] (stn, st))) :: nil)%PropX
      _ _).

    struct.

    destruct st; propxFo.

    specialize (H12 _ _ _ H1); propxFo.
    autorewrite with sepFormula in *; simpl in *.
    Transparent evalInstrs evalInstr.
    simpl in *.
    Opaque evalInstrs.
    Transparent evalRvalue.
    unfold evalRvalue in H15 at 2 3 6.
    Opaque evalRvalue.
    repeat match goal with
             | [ _ : context[match evalRvalue ?A ?B ?C with None => _ | _ => _ end] |- _ ] =>
               case_eq (evalRvalue A B C); intros;
                 match goal with
                   | [ H : _ = _ |- _ ] => rewrite H in *
                 end; try discriminate; simpl in *; autorewrite with IL in *
             | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
           end.
    assert (x1 = w1).
    Transparent evalRvalue.
    simpl in *.
    autorewrite with IL in *.
    congruence.
    subst.
    assert ($(x3) = w0).
    simpl in *.
    autorewrite with IL in *.
    congruence.
    subst.
    Opaque evalRvalue.

    edestruct (@guard_matches s {|
      Regs := rupd
      (rupd (rupd (Regs x0) Rv ($(x3) ^+ $(length p))) Rp
        ($4 ^* $(x3))) Rp (w1 ^+ $4 ^* $(x3));
      Mem := Mem x0 |}).
    eassumption.
    repeat rewrite sepFormula_eq in *; eassumption.
    assumption.
    eassumption.
    simpl; autorewrite with IL.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW; autorewrite with Arr; words.
    eassumption.
    simpl; autorewrite with IL.
    rewrite plus_0_r.
    rewrite natToW_plus.
    unfold natToW; autorewrite with Arr; reflexivity.
    rewrite plus_0_r.
    apply guard_bound in H13; destruct H13 as [ ? [ ] ].
    simpl in *; autorewrite with IL in *.
    eauto.
    simpl in *.

    Hint Extern 2 (_ <> _)%type =>
      match goal with
        | [ H : NoDup _ |- _ ] =>
          repeat match goal with
                   | [ H : NoDup nil |- _ ] => clear H
                   | [ H : NoDup (_ :: _) |- _ ] => inversion H; clear H; intros; subst
                 end; simpl in *; intuition
      end.

    repeat esplit; eauto.
    erewrite reads_leave_alone'; try apply H2; auto.
    erewrite reads_leave_alone'; try apply H2; auto.
    rewrite natToW_plus.
    eapply reads_increment; eauto.
    apply simplify_fwd'; simpl; autorewrite with sepFormula; simpl; eassumption.
    
    (* And then there's the Else case.... *)
    admit.

    (* And the VCs, which definitely aren't provable yet! *)
    admit.
  Defined.

End Parse.
