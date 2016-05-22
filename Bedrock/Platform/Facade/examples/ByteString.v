Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Arrays8.


Definition bytes (capacity : W) (bs : list B) (p : W) : HProp :=
  (Ex capacity', Ex junk,
   [| capacity = capacity' ^* $4 |]
   * [| length bs + length junk = wordToNat capacity' * 4 |]%nat
   * (p ==*> capacity', $(length bs))
   * array8 (bs ++ junk) (p ^+ $8)
   * [| p <> 0 |]
   * [| freeable p (2 + wordToNat capacity') |]
   * [| goodSize (2 + wordToNat capacity') |]
   * [| goodSize (wordToNat capacity' * 4) |])%Sep.

Definition newS := SPEC("extra_stack", "capacity") reserving 7
  PRE[V] [| goodSize (2 + wordToNat (V "capacity") * 4) |] * mallocHeap 0
  POST[R] bytes (V "capacity" ^* $4) nil R * mallocHeap 0.

Definition deleteS := SPEC("extra_stack", "self") reserving 6
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * mallocHeap 0
  POST[R] [| R = $0 |] * mallocHeap 0.

Definition pushS := SPEC("extra_stack", "self", "byte") reserving 38
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * [| length bs + 1 <= wordToNat capacity |]%nat * mallocHeap 0
  POST[R] [| R = $0 |] * bytes capacity (bs ++ WtoB (V "byte") :: nil) (V "self") * mallocHeap 0.

Definition putS := SPEC("extra_stack", "self", "index", "byte") reserving 38
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * [| wordToNat (V "index") < length bs |]%nat * mallocHeap 0
  POST[R] [| R = $0 |] * bytes capacity (PutAt bs (wordToNat (V "index")) (WtoB (V "byte"))) (V "self") * mallocHeap 0.

Definition getS := SPEC("extra_stack", "self", "index") reserving 38
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * [| wordToNat (V "index") < length bs |]%nat * mallocHeap 0
  POST[R] [| R = BtoW (nth (wordToNat (V "index")) bs (wzero _)) |] * bytes capacity bs (V "self") * mallocHeap 0.

Inductive unfold_bytes := UnfoldBytes.
Hint Constructors unfold_bytes.

Definition array8wc bs p (capacity : W) := array8 bs p.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ByteString" {{
    bfunction "new"("extra_stack", "capacity") [newS]
       Assert [PRE[V] [| goodSize (2 + wordToNat (V "capacity")) |] * [| goodSize (wordToNat (V "capacity") * 4) |] * mallocHeap 0
               POST[R] bytes (V "capacity" ^* $4) nil R * mallocHeap 0];;

      "extra_stack" <- 2 + "capacity";;
      "extra_stack" <-- Call "malloc"!"malloc"(0, "extra_stack")
      [PRE[V, R] R =?> (2 + wordToNat (V "capacity")) * [| R <> 0 |] * [| freeable R (2 + wordToNat (V "capacity")) |] * [| goodSize (2 + wordToNat (V "capacity")) |] * [| goodSize (wordToNat (V "capacity") * 4) |]
       POST[R'] bytes (V "capacity" ^* $4) nil R'];;

      "extra_stack" *<- "capacity";;
      "extra_stack" + 4 *<- 0;;
      Return "extra_stack"
    end

    with bfunction "delete"("extra_stack", "self") [deleteS]
       Note [unfold_bytes];;
       Assert [Al capacity', Al bs, Al junk,
               PRE[V] [| length bs + length junk = wordToNat capacity' * 4 |]%nat
                 * (V "self" ==*> capacity', $(length bs))
                 * array8wc (bs ++ junk) (V "self" ^+ $8) capacity'
                 * [| V "self" <> 0 |]
                 * [| freeable (V "self") (2 + wordToNat capacity') |]
                 * [| goodSize (2 + wordToNat capacity') |]
                 * mallocHeap 0
               POST[R] [| R = $0 |] * mallocHeap 0 ];;
       "extra_stack" <-* "self";;
       "extra_stack" <- 2 + "extra_stack";;
       Call "malloc"!"free"(0, "self", "extra_stack")
       [PRE[_] Emp
        POST[R] [| R = $0 |] ];;
       Return 0
    end

    with bfunction "push"("extra_stack", "self", "byte") [pushS]
       Note [unfold_bytes];;
       "extra_stack" <-* "self" + 4;;
       "self" + 4 *<- "extra_stack" + 1;;

       Assert [Al bs,
               PRE[V] array8 bs (V "self" ^+ $8) * [| V "extra_stack" < natToW (length bs) |]%word
               POST[R] [| R = $0 |] * array8 (Array8.upd bs (V "extra_stack") (WtoB (V "byte"))) (V "self" ^+ $8)];;
       "self" <- "self" + 8;;
       "self" + "extra_stack" *<-8 "byte";;
       Return 0
    end

    with bfunction "put"("extra_stack", "self", "index", "byte") [putS]
       Note [unfold_bytes];;
       Assert [Al bs,
               PRE[V] array8 bs (V "self" ^+ $8) * [| V "index" < natToW (length bs) |]%word
               POST[R] [| R = $0 |] * array8 (Array8.upd bs (V "index") (WtoB (V "byte"))) (V "self" ^+ $8)];;
       "self" <- "self" + 8;;
       "self" + "index" *<-8 "byte";;
       Return 0
    end

    with bfunction "get"("extra_stack", "self", "index") [getS]
       Note [unfold_bytes];;
       Assert [Al bs,
               PRE[V] array8 bs (V "self" ^+ $8) * [| V "index" < natToW (length bs) |]%word
               POST[R] [| R = BtoW (Array8.sel bs (V "index")) |] * array8 bs (V "self" ^+ $8)];;
       "self" <- "self" + 8;;
       "self" <-*8 "self" + "index";;
       Return "self"
    end
  }}.

Lemma goodSize_plus_eq : forall (w : W) (n : nat),
    goodSize (n + wordToNat w)
    -> wordToNat (natToW n ^+ w) = n + wordToNat w.
Proof.
  intros.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent; auto.
  change (goodSize n); eauto.
  rewrite wordToNat_natToWord_idempotent; auto.
  change (goodSize n); eauto.
Qed.

Hint Rewrite goodSize_plus_eq using assumption : sepFormula.

Lemma goodSize_plus_le : forall (w : W) (n : nat),
    goodSize (n + wordToNat w)
    -> natToW n <= natToW n ^+ w.
Proof.
  intros.
  pre_nomega.
  autorewrite with sepFormula.
  rewrite wordToNat_natToWord_idempotent; auto.
  change (goodSize n); eauto.
Qed.

Hint Resolve goodSize_plus_le.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma welcome_bytes : forall (p p' : W) capacity,
    p <> 0
    -> freeable p (2 + wordToNat capacity)
    -> goodSize (2 + wordToNat capacity)
    -> goodSize (wordToNat capacity * 4)
    -> p = p'
    -> allocated p 8 (wordToNat capacity) * (p =*> capacity * (p ^+ $4) =*> 0)
       ===> bytes (capacity ^* $4) nil p'.
Proof.
  intros; subst.
  eapply Himp_trans.
  eapply Himp_star_frame.
  eapply Himp_trans.
  apply allocated_shift_base.
  3: apply materialize_array8.
  instantiate (1 := p' ^+ $8).
  words.
  reflexivity.
  apply Himp_refl.
  unfold bytes.
  sepLemma.
Qed.

Hint Extern 1 (himp _ _ _) => apply welcome_bytes.

Lemma farewell_bytes : forall bs junk p (w : W),
    length bs + length junk = wordToNat w * 4
    -> array8wc (bs ++ junk) (p ^+ $8) w
    ===> allocated p 8 (wordToNat w).
Proof.
  intros.
  eapply Himp_trans.
  apply decomission_array8.
  rewrite app_length.
  eassumption.
  apply allocated_shift_base; auto.
  words.
Qed.

Definition hints : TacPackage.
  prepare farewell_bytes tt.
Defined.

Lemma push_bound : forall (bs junk : list B) n,
    (length bs + 1 <= n)%nat
    -> length bs + length junk = n
    -> goodSize n
    -> natToW (length bs) < natToW (length bs + length junk).
Proof.
  intros.
  apply lt_goodSize.
  omega.
  eapply goodSize_weaken; eauto.
  eapply goodSize_weaken; eauto.
Qed.

Hint Extern 1 (_ < natToW (length _)) =>
  autorewrite with sepFormula in *; eapply push_bound.

Lemma goodSize_times4 : forall w : W,
    goodSize (wordToNat w * 4)
    -> wordToNat (w ^* $4) = wordToNat w * 4.
Proof.
  intros.
  rewrite wordToNat_wmult; auto.
Qed.

Hint Rewrite goodSize_times4 using assumption : sepFormula.

Hint Rewrite app_length : sepFormula.

Lemma do_push'' : forall junk b bs,
    (length junk > 0)%nat
    -> Array8.updN (bs ++ junk) (length bs) b
    = ((bs ++ b :: nil) ++ tl junk).
Proof.
  induction bs; simpl; intuition.
  destruct junk; simpl in *; auto.
  omega.
Qed.

Lemma do_push' : forall bs junk b n,
    length bs + length junk = n
    -> (length bs + 1 <= n)%nat
    -> goodSize n
    -> Array8.upd (bs ++ junk) (length bs) b
    = ((bs ++ b :: nil) ++ tl junk).
Proof.
  intros.
  unfold Array8.upd.
  rewrite wordToNat_natToWord_idempotent.
  apply do_push''.
  destruct junk; simpl in *; omega.
  change (goodSize (length bs)).
  eapply goodSize_weaken; eauto.
Qed.

Lemma do_push : forall bs junk b n p,
    length bs + length junk = n
    -> (length bs + 1 <= n)%nat
    -> goodSize n
    -> array8 (Array8.upd (bs ++ junk) (length bs) b) p
       ===> array8 ((bs ++ b :: nil) ++ tl junk) p.
Proof.
  intros.
  erewrite do_push'; eauto.
  apply Himp_refl.
Qed.

Hint Extern 1 (himp _ (array8 (Array8.upd (_ ++ _) _ _) _) _) =>
  autorewrite with sepFormula in *; eapply do_push.

Lemma length_tl : forall A (ls : list A),
    (length ls > 0)%nat
    -> length (tl ls) = length ls - 1.
Proof.
  destruct ls; simpl; omega.
Qed.

Hint Rewrite length_tl using omega : sepFormula.

Hint Extern 1 (@eq nat _ _) => repeat autorewrite with sepFormula in *; omega.

Lemma put_bound : forall i (n m : nat) k,
    (wordToNat i < n)%nat
    -> n + m = k
    -> goodSize k
    -> i < natToW (n + m).
Proof.
  intros; subst.
  replace i with (natToW (wordToNat i)) by apply natToWord_wordToNat.
  apply lt_goodSize.
  auto.
  eapply goodSize_weaken; eauto.
  auto.
Qed.

Hint Immediate put_bound.

Lemma length_PutAt : forall A (ls : list A) n v,
    length (PutAt ls n v) = length ls.
Proof.
  induction ls; destruct n; simpl; intuition.
Qed.

Hint Rewrite length_PutAt : sepFormula.

Lemma PutAt_updN : forall junk b bs i,
    (i < length bs)%nat
    -> Array8.updN (bs ++ junk) i b
    = PutAt bs i b ++ junk.
Proof.
  induction bs; simpl; intuition.
  destruct i; simpl; intuition.
  rewrite IHbs; auto.
Qed.

Lemma PutAt_upd : forall i bs junk b,
    (wordToNat i < length bs)%nat
    -> Array8.upd (bs ++ junk) i b
    = PutAt bs (wordToNat i) b ++ junk.
Proof.
  intros.
  apply PutAt_updN; auto.
Qed.

Lemma PutAt_upd_array8 : forall i bs junk b p,
    (wordToNat i < length bs)%nat
    -> array8 (Array8.upd (bs ++ junk) i b) p
       ===> array8 (PutAt bs (wordToNat i) b ++ junk) p.
Proof.
  intros.
  rewrite PutAt_upd; auto.
  apply Himp_refl.
Qed.

Hint Extern 1 (himp _ _ (array8 (PutAt _ _ _ ++ _) _)) => apply PutAt_upd_array8.

Lemma get_okN : forall junk bs i,
    (i < length bs)%nat
    -> Array8.selN (bs ++ junk) i = nth i bs (wzero _).
Proof.
  induction bs; destruct i; simpl; intuition.
Qed.

Lemma get_ok : forall r bs junk i,
    r = BtoW (Array8.sel (bs ++ junk) i)
    -> (wordToNat i < length bs)%nat
    -> r = BtoW (nth (wordToNat i) bs (wzero _)).
Proof.
  intros; subst.
  unfold Array8.sel.
  rewrite get_okN; auto.
Qed.

Hint Immediate get_ok.

Lemma goodSize1 : forall n,
    goodSize (S (S (n * 4)))
    -> goodSize (S (S n)).
Proof.
  intros.
  eapply goodSize_weaken; eauto.
Qed.

Lemma goodSize2 : forall n,
    goodSize (S (S (n * 4)))
    -> goodSize (n * 4).
Proof.
  intros.
  eapply goodSize_weaken; eauto.
Qed.

Hint Immediate goodSize1 goodSize2.

Ltac t :=
  try match goal with
      | [ |- context[unfold_bytes] ] => unfold bytes, array8wc
      end; sep hints; eauto; eauto.

Theorem ok : moduleOk m.
Proof.
  vcgen.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
Qed.
