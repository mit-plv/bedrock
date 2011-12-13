Require Import List Word PropX IL Env Heaps SepTheoryX.

Set Implicit Arguments.


Fixpoint allWordsUpto (width init : nat) : list (word width) :=
  match init with
    | O => nil
    | S init' => natToWord width init' :: allWordsUpto width init'
  end.

Definition allWords_def (width : nat) :=
  allWordsUpto width (pow2 width).

Fixpoint memoryInUpto (width init : nat) (memHigh : word width) (m : word width -> B)
  : hlist (fun _ => option B) (allWordsUpto width init) :=
  match init with
    | O => HNil
    | S init' =>
      let w := natToWord width init' in
        let v := if wlt_dec w memHigh then Some (m w) else None in
          HCons v (memoryInUpto (width := width) init' memHigh m)
  end.

Definition memoryIn_def (width : nat) (memHigh : word width) :=
  memoryInUpto (width := width) (pow2 width) memHigh.

Theorem fcong : forall A (B : A -> Type) (f g : forall x, B x) x,
  f = g
  -> f x = g x.
  congruence.
Defined.

Module Type ALL_WORDS.
  Parameter allWords : forall width : nat, list (word width).

  Axiom allWords_eq : allWords = allWords_def.

  Parameter memoryIn : forall width, word width -> (word width -> B) -> hlist (fun _ => option B) (allWords width).

  Axiom memoryIn_eq : forall width,
    memoryIn (width := width)
    = match fcong (fun width => list (word width)) width (sym_eq allWords_eq) in _ = L return _ -> _ -> hlist _ L with
        | refl_equal => memoryIn_def (width := width)
      end.
End ALL_WORDS.

Module AllWords : ALL_WORDS.
  Definition allWords := allWords_def.

  Theorem allWords_eq : allWords = allWords_def.
    reflexivity.
  Defined.

  Definition memoryIn := memoryIn_def.

  Theorem memoryIn_eq : forall width,
    memoryIn (width := width)
    = match fcong (fun width => list (word width)) width (sym_eq allWords_eq) in _ = L return _ -> _ -> hlist _ L with
        | refl_equal => memoryIn_def (width := width)
      end.
    reflexivity.
  Qed.
End AllWords.

Import AllWords.
Export AllWords.

Lemma natToWord_injective : forall width n n',
  (n < pow2 width)%nat
  -> (n' < pow2 width)%nat
  -> natToWord width n = natToWord width n'
  -> n = n'.
  intros.
  destruct (wordToNat_natToWord width n);
    destruct (wordToNat_natToWord width n');
      intuition.
  rewrite H1 in H4.
  rewrite H4 in H2.
  assert (x = 0).
  destruct x; simpl in *.
  omega.
  generalize dependent (x * pow2 width).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; simpl in *.
  omega.
  generalize dependent (x0 * pow2 width).
  intros.
  omega.
  subst.
  omega.
Qed.

Local Hint Constructors NoDup.

Lemma NoDup_allWordsUpto' : forall width init' init,
  init <= init' < pow2 width
  -> ~In (natToWord width init') (allWordsUpto width init).
  induction init; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] => apply natToWord_injective in H; omega
    end.
Qed.

Local Hint Resolve NoDup_allWordsUpto'.

Theorem NoDup_allWordsUpto : forall width init,
  (init <= pow2 width)%nat
  -> NoDup (allWordsUpto width init).
  induction init; simpl; intuition.
Qed.

Theorem NoDup_allWords : forall width,
  NoDup (allWords width).
  rewrite allWords_eq; intros; apply NoDup_allWordsUpto; omega.
Qed.

Module BedrockHeap.
  Definition addr := W.
  Definition byte := B.

  Definition mem := mem.

  Definition mem_get (m : mem) (a : addr) := Some (m a).

  Definition addr_dec := @weq 32.

  Definition all_addr := allWords 32.

  Theorem NoDup_all_addr : NoDup all_addr.
    apply NoDup_allWords.
  Qed.
End BedrockHeap.

Module ST := SepTheoryX(BedrockHeap).
Import ST.
Export ST.
Import ST.HT.
Export ST.HT.


Definition memoryIn : W -> mem -> smem := memoryIn (width := 32).

Definition hpropB := hprop W (settings * state).

Definition hptstoB sos : W -> B -> hpropB sos :=
  hptsto W (settings * state) sos.

Notation "a ==> v" := (hptstoB _ a v) (no associativity, at level 39) : Sep_scope.

Definition starB sos : hpropB sos -> hpropB sos -> hpropB sos :=
  @star W (settings * state) sos.

Infix "*" := starB : Sep_scope.

Definition hvarB sos (x : smem -> propX W (settings * state) sos) : hpropB sos :=
  fun _ => x.

Notation "![ x ]" := (hvarB x) : Sep_scope.

Delimit Scope Sep_scope with Sep.

Notation "#0" := (![ #0%PropX ])%Sep : Sep_scope.
Notation "#1" := (![ #1%PropX ])%Sep : Sep_scope.
Notation "#2" := (![ #2%PropX ])%Sep : Sep_scope.
Notation "#3" := (![ #3%PropX ])%Sep : Sep_scope.
Notation "#4" := (![ #4%PropX ])%Sep : Sep_scope.


Definition sepFormula_def sos (p : hpropB sos) (st : settings * state) : propX W (settings * state) sos :=
  p (fst st) (memoryIn (MemHigh (fst st)) (Mem (snd st))).

Module Type SEP_FORMULA.
  Parameter sepFormula : forall sos, hpropB sos -> settings * state -> propX W (settings * state) sos.

  Axiom sepFormula_eq : sepFormula = sepFormula_def.
End SEP_FORMULA.

Module SepFormula : SEP_FORMULA.
  Definition sepFormula := sepFormula_def.

  Theorem sepFormula_eq : sepFormula = sepFormula_def.
    reflexivity.
  Qed.
End SepFormula.

Import SepFormula.
Export SepFormula.

Check subst.

Definition substH sos (p1 : hpropB sos) (p2 : last sos -> PropX W (settings * state)) : hpropB (eatLast sos) :=
  fun st m => subst (p1 st m) p2.

Theorem subst_sepFormula : forall sos (p1 : hpropB sos) p2 st,
  subst (sepFormula p1 st) p2 = sepFormula (substH p1 p2) st.
  rewrite sepFormula_eq; reflexivity.
Qed.

Hint Rewrite subst_sepFormula : sepFormula.

Theorem substH_ptsto : forall sos a v p,
  substH (hptstoB sos a v) p = hptstoB _ a v.
  reflexivity.
Qed.

Hint Rewrite substH_ptsto : sepFormula.

Theorem substH_star : forall sos (p1 p2 : hpropB sos) p3,
  substH (starB p1 p2) p3 = starB (substH p1 p3) (substH p2 p3).
  reflexivity.
Qed.

Hint Rewrite substH_star : sepFormula.

Theorem substH_hvar : forall sos (x : smem -> propX W (settings * state) sos) p,
  substH (hvarB x) p = hvarB (fun m => subst (x m) p).
  reflexivity.
Qed.

Hint Rewrite substH_hvar : sepFormula.

Notation "![ p ]" := (sepFormula p%Sep) : PropX_scope.

Definition natToByte (n : nat) : B := natToWord _ n.

Coercion natToByte : nat >-> B.
