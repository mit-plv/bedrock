Require Import Eqdep_dec List.
Require Import Word PropX PropXTac IL DepList Heaps SepTheoryX.

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
        let v := if wlt_dec w memHigh then if wlt_dec (w ^+ $3) memHigh then Some (m w) else None else None in
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

  Definition mem := mem.

  Definition mem_get (m : mem) (a : addr) := Some (m a).

  Definition mem_set (m : mem) (p : addr) (v : B) := 
    fun p' => if weq p p' then v else m p'.

  Theorem mem_get_set_eq : forall m p v v', 
    mem_get m p = Some v ->
    mem_get (mem_set m p v') p = Some v'.
  Proof.
    unfold mem_set, mem_get. inversion 1; auto.
    destruct (weq p p); auto. congruence.
  Qed.
    
  Theorem mem_get_set_neq : forall m p p' v v', 
    p <> p' ->
    mem_get m p = Some v ->
    mem_get (mem_set m p' v') p = Some v.
  Proof.
    unfold mem_set, mem_get; inversion 2; auto.
    destruct (weq p' p); auto. congruence.
  Qed.

  Definition footprint_w (p : addr) : addr * addr * addr * addr :=
    (p , p ^+ $1 , p ^+ $2 , p ^+ $3).

  Theorem footprint_disjoint : forall p a b c d,
    footprint_w p = (a,b,c,d) ->
    a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d.
  Proof.
    unfold footprint_w. inversion 1. clear.
    repeat split; W_neq.
  Qed.

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

(** * Define some convenient connectives, etc. for specs *)
Definition memoryIn : W -> mem -> smem := memoryIn (width := 32).

Definition hpropB := hprop W (settings * state).
Definition HProp := hpropB nil.

Definition injB sos (P : Prop) : hpropB sos := inj (Inj P).

Notation "[| P |]" := (injB _ P) : Sep_scope.

Definition injBX sos (P : propX W (settings * state) sos) : hpropB sos := inj P.

Notation "[|| P ||]" := (injBX P) : Sep_scope.

Definition ptsto8 sos : W -> B -> hpropB sos :=
  hptsto W (settings * state) sos.

Notation "a =8> v" := (ptsto8 _ a v) (no associativity, at level 39) : Sep_scope.

(* This breaks the hprop abstraction because it needs access to 'settings' *)
Definition ptsto32 sos (a v : W) : hpropB sos :=
  (fun stn sm => [| exists b0, exists b1, exists b2, exists b3,
    smem_get a sm = Some b0
    /\ smem_get (a ^+ $1) sm = Some b1
    /\ smem_get (a ^+ $2) sm = Some b2
    /\ smem_get (a ^+ $3) sm = Some b3
    /\ (forall a', a' <> a -> a' <> a ^+ $1 -> a' <> a ^+ $2 -> a' <> a ^+ $3 -> smem_get a' sm = None)
    /\ implode stn (b0, b1, b2, b3) = v |])%PropX.

Notation "a ==> v" := (ptsto32 _ a v) (no associativity, at level 39) : Sep_scope.

Definition starB sos : hpropB sos -> hpropB sos -> hpropB sos :=
  @star W (settings * state) sos.

Infix "*" := starB : Sep_scope.

Definition exB sos T (p : T -> hpropB sos) : hpropB sos := ex p.

Notation "'Ex' x , p" := (exB (fun x => p)) : Sep_scope.
Notation "'Ex' x : A , p" := (exB (fun x : A => p)) : Sep_scope.

Definition hvarB sos (x : smem -> propX W (settings * state) sos) : hpropB sos :=
  fun _ => x.

Notation "![ x ]" := (hvarB x) : Sep_scope.

Delimit Scope Sep_scope with Sep.

Notation "#0" := (![ #0%PropX ])%Sep : Sep_scope.
Notation "#1" := (![ #1%PropX ])%Sep : Sep_scope.
Notation "#2" := (![ #2%PropX ])%Sep : Sep_scope.
Notation "#3" := (![ #3%PropX ])%Sep : Sep_scope.
Notation "#4" := (![ #4%PropX ])%Sep : Sep_scope.

Definition Himp (p1 p2 : HProp) : Prop :=
  forall specs, ST.himp specs p1 p2.

Notation "p1 ===> p2" := (Himp p1%Sep p2%Sep) (no associativity, at level 90).

(** * The main injector of separation formulas into PropX *)

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

Definition substH sos (p1 : hpropB sos) (p2 : last sos -> PropX W (settings * state)) : hpropB (eatLast sos) :=
  fun st m => subst (p1 st m) p2.

Theorem subst_sepFormula : forall sos (p1 : hpropB sos) p2 st,
  subst (sepFormula p1 st) p2 = sepFormula (substH p1 p2) st.
  rewrite sepFormula_eq; reflexivity.
Qed.

Hint Rewrite subst_sepFormula : sepFormula.

Theorem substH_inj : forall sos P p,
  substH (injB sos P) p = injB _ P.
  reflexivity.
Qed.

Theorem substH_injX : forall sos P p,
  substH (injBX (sos := sos) P) p = injBX (subst P p).
  reflexivity.
Qed.

Theorem substH_ptsto8 : forall sos a v p,
  substH (ptsto8 sos a v) p = ptsto8 _ a v.
  reflexivity.
Qed.

Theorem substH_ptsto32 : forall sos a v p,
  substH (ptsto32 sos a v) p = ptsto32 _ a v.
  reflexivity.
Qed.

Theorem substH_star : forall sos (p1 p2 : hpropB sos) p3,
  substH (starB p1 p2) p3 = starB (substH p1 p3) (substH p2 p3).
  reflexivity.
Qed.

Theorem substH_ex : forall sos A (p1 : A -> hpropB sos) p2,
  substH (exB p1) p2 = exB (fun x => substH (p1 x) p2).
  reflexivity.
Qed.

Theorem substH_hvar : forall sos (x : smem -> propX W (settings * state) sos) p,
  substH (hvarB x) p = hvarB (fun m => subst (x m) p).
  reflexivity.
Qed.

Hint Rewrite substH_inj substH_injX substH_ptsto8 substH_ptsto32 substH_star substH_ex substH_hvar : sepFormula.

Notation "![ p ]" := (sepFormula p%Sep) : PropX_scope.

Definition natToByte (n : nat) : B := natToWord _ n.

Coercion natToByte : nat >-> B.


(** Isolating a byte points-to fact within a separation assertion *)

Definition findPtsto8 (h : hpropB nil) (a : W) (v : B) :=
  forall specs stn m, interp specs (h stn m)
    -> smem_get a m = Some v.

Theorem findPtsto8_gotIt : forall a v,
  findPtsto8 (ptsto8 _ a v) a v.
  unfold findPtsto8; propxFo.
Qed.

Lemma join'1 : forall a v dom (m1 m2 : smem' dom),
  smem_get' _ a m1 = Some v
  -> smem_get' _ a (join' _ m1 m2) = Some v.
  induction dom; simpl; intuition;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; subst; auto.
  rewrite H; reflexivity.
Qed.

Theorem join1 : forall m1 m2 a v,
  smem_get a m1 = Some v
  -> smem_get a (join m1 m2) = Some v.
  intros; apply join'1; auto.
Qed.

Local Hint Resolve join1.

Theorem findPtsto8_star1 : forall p1 p2 a v,
  findPtsto8 p1 a v
  -> findPtsto8 (starB p1 p2) a v.
  unfold findPtsto8; propxFo.
  apply H in H0.
  destruct H1; subst; auto.
Qed.

Lemma join'2 : forall a v dom (m1 m2 : smem' dom),
  smem_get' _ a m1 = None
  -> smem_get' _ a m2 = Some v
  -> smem_get' _ a (join' _ m1 m2) = Some v.
  induction dom; simpl; intuition;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; subst; auto.
  rewrite H; assumption.
Qed.

Theorem join2 : forall m1 m2 a v,
  smem_get a m1 = None
  -> smem_get a m2 = Some v
  -> smem_get a (join m1 m2) = Some v.
  intros; apply join'2; auto.
Qed.

Lemma disjoint'_correct : forall a v dom (m1 m2 : smem' dom),
  disjoint' _ m1 m2
  -> smem_get' _ a m2 = Some v
  -> smem_get' _ a m1 = None.
  induction dom; simpl; intuition;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; subst; eauto.
  congruence.
Qed.

Lemma disjoint_correct : forall a v m1 m2,
  disjoint m1 m2
  -> smem_get a m2 = Some v
  -> smem_get a m1 = None.
  intros; eapply disjoint'_correct; eauto.
Qed.

Local Hint Resolve disjoint_correct.

Theorem findPtsto8_star2 : forall p1 p2 a v,
  findPtsto8 p2 a v
  -> findPtsto8 (starB p1 p2) a v.
  unfold findPtsto8; propxFo.
  apply H in H3.
  destruct H1; subst; auto.
  apply join2; auto.
  eauto.
Qed.

Lemma findPtsto8_inBounds'1 : forall a v (memHigh : W) m init,
  smem_get' _ a (memoryInUpto init memHigh m) = Some v
  -> a < memHigh.
  induction init.
  simpl; congruence.
  unfold allWordsUpto.
  fold allWordsUpto.
  unfold smem_get'; fold smem_get'.
  destruct (BedrockHeap.addr_dec (natToWord _ init) a); subst.
  unfold memoryInUpto; fold memoryInUpto.
  destruct (wlt_dec (natToWord _ init) memHigh); intuition.
  discriminate.
  auto.
Qed.

Lemma findPtsto8_inBounds'2 : forall a v (memHigh : W) m init,
  smem_get' _ a (memoryInUpto init memHigh m) = Some v
  -> a ^+ $3 < memHigh.
  induction init.
  simpl; congruence.
  unfold allWordsUpto.
  fold allWordsUpto.
  unfold smem_get'; fold smem_get'.
  destruct (BedrockHeap.addr_dec (natToWord _ init) a); subst; auto.
  unfold memoryInUpto; fold memoryInUpto.
  destruct (wlt_dec (natToWord _ init) memHigh); intuition.
  destruct (wlt_dec (natToWord _ init ^+ natToWord _ 3) memHigh); intuition.
  discriminate.
  discriminate.
Qed.

Local Opaque pow2.

Lemma smem_get_inBounds : forall stn a v m,
  smem_get a (memoryIn (MemHigh stn) m) = Some v
  -> inBounds stn a.
  unfold memoryIn; rewrite AllWords.memoryIn_eq; intros ? ? ? ?.
  unfold smem_get, BedrockHeap.all_addr.
  match goal with
    | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
  end.
  rewrite allWords_eq; intros.
  rewrite (UIP_dec (list_eq_dec (@weq _)) e (refl_equal _)) in H.
  unfold memoryIn_def, allWords_def in H.
  split.
  apply findPtsto8_inBounds'1 with v m (pow2 32); assumption.
  apply findPtsto8_inBounds'2 with v m (pow2 32); assumption.
Qed.

Theorem findPtsto8_inBounds : forall specs p st,
  interp specs (sepFormula p st)
  -> forall a v, findPtsto8 p a v
    -> ~inBounds (fst st) a
    -> False.
  rewrite sepFormula_eq; intros.
  apply H0 in H.
  apply smem_get_inBounds in H.
  tauto.
Qed.

Lemma smem_get'_read : forall a v (memHigh : W) m init,
  smem_get' _ a (memoryInUpto init memHigh m) = Some v
  -> m a = v.
  induction init.
  simpl; congruence.
  unfold allWordsUpto.
  fold allWordsUpto.
  unfold smem_get'; fold smem_get'.
  destruct (BedrockHeap.addr_dec (natToWord _ init) a); subst.
  unfold memoryInUpto; fold memoryInUpto.
  destruct (wlt_dec (natToWord _ init) memHigh); intuition.
  destruct (wlt_dec (natToWord _ init ^+ natToWord _ 3) memHigh); intuition.
  unfold hlist_hd in H.
  congruence.
  discriminate.
  discriminate.
  auto.
Qed.

Lemma smem_get_read : forall stn a v m,
  smem_get a (memoryIn (MemHigh stn) m) = Some v
  -> m a = v.
  unfold memoryIn; rewrite AllWords.memoryIn_eq; intros ? ? ? ?.
  unfold smem_get, BedrockHeap.all_addr.
  match goal with
    | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
  end.
  rewrite allWords_eq; intros.
  rewrite (UIP_dec (list_eq_dec (@weq _)) e (refl_equal _)) in H.
  unfold memoryIn_def, allWords_def in H.
  apply smem_get'_read with (MemHigh stn) (pow2 32); assumption.
Qed.

Theorem findPtsto8_read : forall specs p st,
  interp specs (sepFormula p st)
  -> forall a v, findPtsto8 p a v
    -> Mem (snd st) a = v.
  rewrite sepFormula_eq; intros.
  apply H0 in H.
  eapply smem_get_read; eauto.
Qed.


(** Isolating a word points-to fact within a separation assertion *)

Definition findPtsto32 (stn : settings) (h : hpropB nil) (a v : W) :=
  forall specs sm, interp specs (h stn sm)
    -> exists b0, exists b1, exists b2, exists b3,
      smem_get a sm = Some b0
      /\ smem_get (a ^+ $1) sm = Some b1
      /\ smem_get (a ^+ $2) sm = Some b2
      /\ smem_get (a ^+ $3) sm = Some b3
      /\ implode stn (b0, b1, b2, b3) = v.

Theorem findPtsto32_gotIt : forall stn a v,
  findPtsto32 stn (ptsto32 _ a v) a v.
  unfold findPtsto32; propxFo; eauto 10.
Qed.

Theorem findPtsto32_star1 : forall stn p1 p2 a v,
  findPtsto32 stn p1 a v
  -> findPtsto32 stn (starB p1 p2) a v.
  unfold findPtsto32; propxFo.
  apply H in H0; clear H; propxFo.
  destruct H1; subst; eauto 13.
Qed.

Theorem findPtsto32_star2 : forall stn p1 p2 a v,
  findPtsto32 stn p2 a v
  -> findPtsto32 stn (starB p1 p2) a v.
  unfold findPtsto32; propxFo.
  apply H in H3; clear H; propxFo.
  destruct H1; subst.
  repeat esplit; eauto; apply join2; eauto.
Qed.

Theorem findPtsto32_inBounds : forall specs p st,
  interp specs (sepFormula p st)
  -> forall a v, findPtsto32 (fst st) p a v
    -> ~inBounds (fst st) a
    -> False.
  rewrite sepFormula_eq; intros.
  apply H0 in H; clear H0; propxFo.
  apply smem_get_inBounds in H0.
  tauto.
Qed.

Theorem findPtsto32_read : forall specs p stn st,
  interp specs (sepFormula p (stn, st))
  -> forall a v, findPtsto32 stn p a v
    -> ReadWord stn (Mem st) a = v.
  rewrite sepFormula_eq; intros.
  apply H0 in H; clear H0; propxFo.
  unfold ReadWord. simpl in *.
  repeat match goal with
           | [ H : _ |- _ ] => apply smem_get_read in H; rewrite H
         end.
  auto.
Qed.


(** * Tactics *)

Ltac findPtsTo8 :=
  apply findPtsto8_gotIt || (apply findPtsto8_star1; findPtsTo8)
    || (apply findPtsto8_star2; findPtsTo8).

Ltac findPtsTo32 :=
  apply findPtsto32_gotIt || (apply findPtsto32_star1; findPtsTo32)
    || (apply findPtsto32_star2; findPtsTo32).

Ltac inBounds_contra8 := eapply findPtsto8_inBounds; [ eassumption | findPtsTo8 | assumption ].
Ltac inBounds_contra32 := eapply findPtsto32_inBounds; [ eassumption | findPtsTo32 | assumption ].

Ltac inBounds_contra := inBounds_contra8 || inBounds_contra32.

Hint Extern 1 False => inBounds_contra.

Ltac sepRead := match goal with
                  | [ H : interp _ _ |- _ ] => erewrite (findPtsto32_read H); [ | findPtsTo32 ]
                end.
