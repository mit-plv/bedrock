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
      /\ ExX, Ex V, Ex ws, Ex r,
      ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st')
      /\ [| matches p (suffix (wordToNat (sel V pos)) ws) |]
      /\ ![ ^[array ws (sel V stream) * locals ("rp" :: ns)
        (upd
          (fold_left (fun V p => upd V (fst p) (snd p)) (binds p (suffix (wordToNat (sel V pos)) ws)) V)
          pos (sel V pos ^+ $(length p))) r (Regs st Sp)]
      * #0] (stn, st')
      /\ [| Regs st Sp = Regs st' Sp |])%PropX.

  Definition ElsePre (pre : assert) : assert :=
    (fun stn_st => let (stn, st) := stn_st in
      Ex st', pre (stn, st')
      /\ ExX, Ex V, Ex ws, Ex r,
        ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st')
        /\ [| ~matches p (suffix (wordToNat (sel V pos)) ws)|]
        /\ ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st)
        /\ [| Regs st Sp = Regs st' Sp |])%PropX.

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

  Lemma bexpSafe_guard : forall specs stn st ws V r fr posV,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* posV
    -> forall p' offset,
      (wordToNat posV + offset + length p' <= length ws)%nat
      -> bexpSafe (guard p' offset) stn st.
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    prep_locals; evaluate auto_ext.

    replace (evalCond (LvMem (Rp + 4 * offset)%loc) IL.Eq w stn st)
      with (evalCond (LvMem (Imm (sel V stream ^+ $4 ^* $(offset + wordToNat posV)))) IL.Eq w stn st) in *.
    assert (goodSize (length ws)) by eauto.
    assert (natToW (offset + wordToNat posV) < $(length ws)) by eauto.
    
    evaluate auto_ext.
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
  Qed.

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
            /\ [| sel V size = length ws
              /\ goodSize (length ws + length p)
              /\ (wordToNat (sel V pos) + length p <= length ws)%nat  |]))%PropX
        :: VerifCond (Then (ThenPre pre))
        ++ VerifCond (Else (ElsePre pre)))
      _); wrap.

    clear_fancy; evaluate auto_ext.

    clear_fancy; evaluate auto_ext.
    eapply bexpSafe_guard; eauto.
    instantiate (4 := specs); step auto_ext.
    auto.

    clear_fancy.
    generalize dependent H14.
    evaluate auto_ext.
    clear H17; intro.
    admit. (* Needs [reads] reasoning *)

    admit. (* Needs [reads] reasoning *)

    generalize H13.
    clear_fancy; evaluate auto_ext; intro Hold.
    eexists; split.
    eauto.
    repeat esplit; eauto.
    apply simplify_fwd'; simpl; autorewrite with sepFormula; simpl; step auto_ext.
    admit. (* Needs bexpFalse -> ~matches *)
    apply simplify_fwd'; simpl; autorewrite with sepFormula; simpl; step auto_ext.
  Defined.

End Parse.
