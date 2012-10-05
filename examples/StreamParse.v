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

Fixpoint matches (p : pattern) (ws : list W) : Prop :=
  match p, ws with
    | nil, _ => True
    | Const_ w :: p', w' :: ws' => w = w' /\ matches p' ws'
    | Var_ _ :: p', _ :: ws' => matches p' ws'
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
      | Var_ x :: p' => Assign (variableSlot x ns) (LvMem (Indir Rp (4 * offset))) :: reads p' (S offset)
    end.

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

  Fixpoint patternBound (p : pattern) : Prop :=
    match p with
      | nil => True
      | Const_ _ :: p' => patternBound p'
      | Var_ x :: p' => In x ns /\ patternBound p'
    end.

  Fixpoint okVarName (x : string) (p : pattern) : Prop :=
    match p with
      | nil => True
      | Const_ _ :: p' => okVarName x p'
      | Var_ x' :: p' => if string_dec x x' then False else okVarName x p'
    end.

  Definition ThenPre (pre : assert) : assert :=
    (fun stn_st => let (stn, st) := stn_st in
      Ex st', pre (stn, st')
      /\ (AlX, Al V, Al ws, Al r,
        ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st')
        /\ [| sel V size = length ws |]
        ---> [| matches p (suffix (wordToNat (sel V pos)) ws)
          /\ exists st'', Mem st'' = Mem st
            /\ evalInstrs stn st'' (map (fun p => Assign (variableSlot (fst p) ns) (RvImm (snd p)))
              (binds p (suffix (wordToNat (sel V pos)) ws))
              ++ Binop (variableSlot pos ns) (variableSlot pos ns) Plus 1
              :: nil) = Some st' |])
      /\ [| Regs st Sp = Regs st' Sp |])%PropX.

  Definition ElsePre (pre : assert) : assert :=
    (fun stn_st => let (stn, st) := stn_st in
      Ex st', pre (stn, st')
      /\ (AlX, Al V, Al ws, Al r,
        ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st')
        /\ [| sel V size = length ws |]
        ---> [| ~matches p (suffix (wordToNat (sel V pos)) ws) |])
      /\ [| Regs st Sp = Regs st' Sp /\ Mem st = Mem st' |])%PropX.

  (* Here's the raw parsing command, which we will later wrap with nicer VCs. *)
  Definition Parse1_ : cmd imports modName := fun pre =>
    Seq_ H (Straightline_ _ _ (Binop Rv (variableSlot pos ns) Plus (length p)
      :: Binop Rp 4 Times (variableSlot pos ns)
      :: Binop Rp (variableSlot stream ns) Plus Rp
      :: nil))
    (Cond_ _ H _ (guard p O)
      (Seq_ H
        (Straightline_ _ _ (reads p O
          ++ Binop (variableSlot pos ns) (variableSlot pos ns) Plus (length p)
          :: nil))
        (Seq_ H
          (Structured.Assert_ _ _ (ThenPre pre))
          Then))
      (Seq_ H
        (Structured.Assert_ _ _ (ElsePre pre))
        Else))
    pre.

  Lemma four_plus_variablePosition : forall x ns',
    ~In "rp" ns'
    -> In x ns'
    -> 4 + variablePosition ns' x = variablePosition ("rp" :: ns') x.
    unfold variablePosition at 2; intros.
    destruct (string_dec "rp" x); auto; subst; tauto.
  Qed.

  Ltac prep_locals :=
    unfold variableSlot in *; repeat rewrite four_plus_variablePosition in * by assumption;
      repeat match goal with
               | [ H : In ?X ?ls |- _ ] =>
                 match ls with
                   | "rp" :: _ => fail 1
                   | _ =>
                     match goal with
                       | [ _ : In X ("rp" :: ls) |- _ ] => fail 1
                       | _ => assert (In X ("rp" :: ls)) by (simpl; tauto)
                     end
                 end
             end.

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
    -> (m <= n)%nat
    -> goodSize m.
    unfold goodSize; generalize 32; intros; nomega.
  Qed.

  Hint Resolve lt_goodSize goodSize_weaken.
  Hint Extern 1 (_ <= _)%nat => omega.

  Opaque mult.

  Lemma bexpTrue_bound : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> forall p' offset, bexpTrue (guard p' offset) stn st
      -> Regs st Rv <= sel V size.
    clear H; induction p' as [ | [ ] ]; simpl; intuition eauto.

    prep_locals; evaluate auto_ext; tauto.
  Qed.

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

  Lemma bexpSafe_guard : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
    -> sel V size = $(length ws)
    -> forall p' offset,
      Regs st Rv = $(offset + wordToNat (sel V pos) + length p')
      -> goodSize (offset + wordToNat (sel V pos) + Datatypes.length p')
      -> bexpSafe (guard p' offset) stn st.
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    prep_locals; evaluate auto_ext.

    apply IHp'.
    rewrite H4; f_equal; omega.
    eauto.

    replace (evalCond (LvMem (Rp + 4 * offset)%loc) IL.Eq w stn st)
      with (evalCond (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat (sel V pos))))) IL.Eq w stn st)
        in *.
    assert (goodSize (length ws)) by eauto.
    assert (natToW (offset + wordToNat (sel V pos)) < $(length ws)).
    specialize (bexpTrue_bound _ H H0 H1 _ _ H6).
    rewrite H3, H4.
    intros.
    apply wle_goodSize in H9; auto; eauto.

    prep_locals; evaluate auto_ext.

    unfold evalCond; simpl.
    rewrite H2.
    match goal with
      | [ |- match ReadWord _ _ ?X with None => _ | _ => _ end
        = match ReadWord _ _ ?Y with None => _ | _ => _ end ] => replace Y with X; auto
    end.
    rewrite mult_comm; rewrite natToW_times4.
    rewrite natToW_plus.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    apply IHp'; eauto.
    rewrite H4; f_equal; omega.
  Qed.

  Lemma bexpTrue_matches : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
    -> forall p' offset, bexpTrue (guard p' offset) stn st
      -> Regs st Rv = $(offset + wordToNat (sel V pos) + length p')
      -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
      -> matches p' (suffix (offset + wordToNat (sel V pos)) ws).
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    specialize (bexpTrue_bound _ H H0 H1 _ _ H6).
    rewrite H4; intros.
    rewrite suffix_remains in * by auto.
    replace (evalCond (LvMem (Rp + 4 * offset)%loc) IL.Eq w stn st)
      with (evalCond (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat (sel V pos))))) IL.Eq w stn st)
        in *.
    assert (natToW (offset + wordToNat (sel V pos)) < natToW (length ws))
      by (apply lt_goodSize; eauto).
    prep_locals; evaluate auto_ext.
    split.
    subst.
    unfold Array.sel.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize (offset + wordToNat (sel V pos))); eauto.
    change (S (offset + wordToNat (sel V pos))) with (S offset + wordToNat (sel V pos)).
    apply IHp'; auto.
    rewrite H4; f_equal; omega.

    unfold evalCond; simpl.
    rewrite H2.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    rewrite suffix_remains in * by auto.
    change (S (offset + wordToNat (sel V pos))) with (S offset + wordToNat (sel V pos)).
    apply IHp'; auto.
    rewrite H4; f_equal; omega.
  Qed.

  Theorem le_goodSize : forall n m,
    (n <= m)%nat
    -> goodSize n
    -> goodSize m
    -> natToW n <= natToW m.
    unfold goodSize, natToW, W; generalize 32; intros; nomega.
  Qed.

  Lemma bexpFalse_not_matches : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
    -> sel V size = $(length ws)
    -> forall p' offset, bexpFalse (guard p' offset) stn st
      -> Regs st Rv = $(offset + wordToNat (sel V pos) + length p')
      -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
      -> ~matches p' (suffix (offset + wordToNat (sel V pos)) ws).
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    prep_locals; evaluate auto_ext.
    rewrite H3 in *.
    apply le_goodSize in H6; eauto.

    rewrite suffix_remains in * by auto.
    intuition; subst.
    eapply IHp'; eauto.
    rewrite H5; f_equal; omega.

    specialize (bexpTrue_bound _ H H0 H1 _ _ H4).
    rewrite H5; intros.
    rewrite suffix_remains in * by auto.
    replace (evalCond (LvMem (Rp + 4 * offset)%loc) IL.Eq w stn st)
      with (evalCond (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat (sel V pos))))) IL.Eq w stn st)
        in *.
    assert (natToW (offset + wordToNat (sel V pos)) < natToW (length ws))
      by (apply lt_goodSize; eauto).
    prep_locals; evaluate auto_ext.
    subst.
    apply H15.
    unfold Array.sel.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize (offset + wordToNat (sel V pos))); eauto.

    unfold evalCond; simpl.
    rewrite H2.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    rewrite suffix_remains in * by auto.
    intuition; subst.
    eapply IHp'; eauto.
    rewrite H5; f_equal; omega.
  Qed.

  Transparent evalInstrs.

  Lemma evalInstrs_app_fwd : forall stn is2 st' is1 st,
    evalInstrs stn st (is1 ++ is2) = Some st'
    -> exists st'', evalInstrs stn st is1 = Some st''
      /\ evalInstrs stn st'' is2 = Some st'.
    induction is1; simpl; intuition eauto.
    destruct (evalInstr stn st a); eauto; discriminate.
  Qed.

  Opaque evalInstr.

  Lemma evalInstr_evalInstrs : forall stn st i,
    evalInstr stn st i = evalInstrs stn st (i :: nil).
    simpl; intros; destruct (evalInstr stn st i); auto.
  Qed.

  Lemma reads_nocrash : forall specs stn ws r fr,
    ~In "rp" ns
    -> forall p' offset st V, patternBound p'
      -> interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
      -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
      -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
      -> okVarName stream p'
      -> okVarName pos p'
      -> evalInstrs stn st (reads p' offset) = None
      -> False.
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    eapply IHp'; eauto.
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.

    destruct (string_dec stream s); try tauto.
    destruct (string_dec pos s); try tauto.

    case_eq (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc))); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $(length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.
    intros.
    eapply IHp'.
    eauto.
    instantiate (1 := s0).
    step auto_ext.
    reflexivity.
    repeat rewrite sel_upd_ne by congruence.
    assumption.
    instantiate (1 := S offset).
    repeat rewrite sel_upd_ne by congruence.    
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.
    assumption.
    assumption.
    assumption.
    Transparent evalInstr.
    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $(length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.

    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.
  Qed.

  Opaque evalInstr.

  Lemma reads_exec : forall specs stn ws r fr,
    ~In "rp" ns
    -> forall p' offset st st' V, patternBound p'
      -> interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
      -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
      -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
      -> okVarName stream p'
      -> okVarName pos p'
      -> evalInstrs stn st (reads p' offset) = Some st'
      -> exists V',
        interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V' r (Regs st Sp) * fr] (stn, st'))
        /\ Regs st' Sp = Regs st Sp.
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    injection H6; intros; subst.
    eauto.

    eapply IHp'; eauto.
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.

    destruct (string_dec stream s); try tauto.
    destruct (string_dec pos s); try tauto.

    case_eq (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc))); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $(length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.
    intros.
    eapply (IHp' _ _ _ (upd V s (Array.sel ws (offset + wordToNat (sel V pos))))) in H13.
    rewrite <- H1.
    rewrite sel_upd_ne in H13 by congruence.
    assumption.
    eauto.
    step auto_ext.
    reflexivity.
    rewrite H10.
    repeat rewrite sel_upd_ne by congruence.
    W_eq.
    repeat rewrite sel_upd_ne by congruence.
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.
    assumption.
    assumption.
    Transparent evalInstr.
    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $(length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.

    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.
  Qed.

  Lemma evalInstrs_app_fwd_None : forall stn is2 is1 st,
    evalInstrs stn st (is1 ++ is2) = None
    -> evalInstrs stn st is1 = None
    \/ (exists st', evalInstrs stn st is1 = Some st' /\ evalInstrs stn st' is2 = None).
    induction is1; simpl; intuition eauto.
    destruct (evalInstr stn st a); eauto.
  Qed.

  Opaque evalInstrs.

  Ltac wrap :=
    intros;
      repeat match goal with
               | [ H : vcs nil |- _ ] => clear H
               | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; intros; subst
               | [ H : vcs (_ ++ _) |- _ ] => specialize (vcs_app_bwd1 _ _ H);
                 specialize (vcs_app_bwd2 _ _ H); clear H; intros
             end; simpl;
      repeat match goal with
               | [ |- vcs nil ] => constructor
               | [ |- vcs (_ :: _) ] => constructor
               | [ |- vcs (_ ++ _) ] => apply vcs_app_fwd
             end; propxFo;
    try match goal with
          | [ H : forall stn : settings, _, H' : interp _ _ |- _ ] =>
            specialize (H _ _ _ H')
        end; post; prep_locals; auto.

  Ltac clear_fancy := try clear H;
    repeat match goal with
             | [ H : vcs _ |- _ ] => clear H
           end.

  Definition Parse1 : cmd imports modName.
    refine (Wrap _ H _ Parse1_
      (fun pre =>
        (N_of_nat (length ns) < Npow2 30)%N
        :: In stream ns
        :: In size ns
        :: In pos ns
        :: (~In "rp" ns)
        :: patternBound p
        :: okVarName stream p
        :: okVarName size p
        :: okVarName pos p
        :: NoDup (stream :: size :: pos :: nil)
        :: (forall stn st specs,
          interp specs (pre (stn, st))
          -> interp specs (ExX, Ex V, Ex ws, Ex r,
            ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st)
            /\ [| sel V size = length ws /\ goodSize (wordToNat (sel V pos) + length p) |]))%PropX
        :: VerifCond (Then (ThenPre pre))
        ++ VerifCond (Else (ElsePre pre)))
      _); wrap.

    Opaque variablePosition.

    clear_fancy; evaluate auto_ext.


    clear_fancy; evaluate auto_ext.
    eapply bexpSafe_guard; eauto.
    instantiate (3 := specs); step auto_ext.
    rewrite H1.
    simpl.
    rewrite natToW_plus.
    f_equal.
    symmetry; apply natToWord_wordToNat.

    
    clear_fancy; generalize dependent H14; evaluate auto_ext; intro H14.
    apply evalInstrs_app_fwd_None in H14.
    destruct H14.
    eapply reads_nocrash; eauto.
    instantiate (4 := specs); step auto_ext.
    simpl.
    apply wle_goodSize.
    rewrite natToW_plus.
    unfold natToW; rewrite natToWord_wordToNat.
    change (fix length (l : list pattern0) : nat :=
      match l with
        | nil => 0
        | _ :: l' => S (length l')
      end) with (@length pattern0) in H1.
    unfold natToW in H1, H12.
    rewrite <- H1.
    rewrite <- H12.
    eapply bexpTrue_bound; eauto.
    instantiate (4 := specs); step auto_ext.
    assumption.
    eauto.
    destruct H14 as [ ? [ ] ].
    eapply reads_exec in H14; eauto.
    2: instantiate (4 := specs); step auto_ext.
    simpl in H14; destruct H14 as [V' [ ] ].
    evaluate auto_ext.
    simpl.
    apply wle_goodSize.
    rewrite natToW_plus.
    unfold natToW; rewrite natToWord_wordToNat.
    change (fix length (l : list pattern0) : nat :=
      match l with
        | nil => 0
        | _ :: l' => S (length l')
      end) with (@length pattern0) in H1.
    unfold natToW in H1, H12.
    rewrite <- H1.
    rewrite <- H12.
    eapply bexpTrue_bound; eauto.
    instantiate (4 := specs); step auto_ext.
    assumption.
    eauto.

    
    clear_fancy; generalize dependent H15; evaluate auto_ext; intro H15.
    apply evalInstrs_app_fwd in H15; destruct H15 as [ ? [ ] ].
    eapply reads_exec in H15; eauto.
    2: instantiate (4 := specs); step auto_ext.
    simpl in H15; destruct H15 as [V' [ ] ].
    evaluate auto_ext.
    eexists; split.
    apply simplify_fwd; eassumption.
    intuition.
    autorewrite with sepFormula; simpl.
    (* needs [array] and [locals] uniqueness reasoning *)
    admit.

    simpl.
    apply wle_goodSize.
    rewrite natToW_plus.
    unfold natToW; rewrite natToWord_wordToNat.
    change (fix length (l : list pattern0) : nat :=
      match l with
        | nil => 0
        | _ :: l' => S (length l')
      end) with (@length pattern0) in H1.
    unfold natToW in H1, H12.
    rewrite <- H1.
    rewrite <- H12.
    eapply bexpTrue_bound; eauto.
    instantiate (4 := specs); step auto_ext.
    assumption.
    eauto.


    clear_fancy; evaluate auto_ext.
    eexists; split.
    apply simplify_fwd; eassumption.
    intuition.
    autorewrite with sepFormula; simpl.
    (* needs [array] and [locals] uniqueness reasoning *)
    admit.

    generalize H16; clear.
    Transparent evalInstrs.
    simpl.
    repeat match goal with
             | [ |- context[match ?E with None => _ | _ => _ end] ] =>
               match E with
                 | context[match _ with None => _ | _ => _ end] => fail 1
                 | _ => destruct E
               end
           end; simpl; inversion 1; subst; reflexivity.
  Defined.

End Parse.
