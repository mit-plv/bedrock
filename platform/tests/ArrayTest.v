Require Import Arith AutoSep.


Definition readS := SPEC("arr", "pos") reserving 0
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "pos" < $(length arr) |]
  POST[R] array8 arr (V "arr") * [| R = BtoW (Array8.sel arr (V "pos")) |].

Definition writeS := SPEC("arr", "pos", "val") reserving 0
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "pos" < $(length arr) |]
  POST[_] array8 (Array8.upd arr (V "pos") (WtoB (V "val"))) (V "arr").

Definition inc1 (b : B) : B := WtoB (BtoW b ^+ $1).
Definition inc := map inc1.

Definition incS := SPEC("arr", "len") reserving 2
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "len" = length arr |] * [| goodSize (length arr) |]
  POST[_] array8 (inc arr) (V "arr").

Definition sum ls := fold_left (fun n b => n ^+ BtoW b) ls $0.

Definition sumS := SPEC("arr", "len") reserving 3
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "len" = length arr |] * [| goodSize (length arr) |]
  POST[R] array8 arr (V "arr") * [| R = sum arr |].

Definition m := bmodule "array" {{
  bfunction "read"("arr", "pos") [readS]
    "arr" <-*8 "arr" + "pos";;
    Return "arr"
  end with bfunction "write"("arr", "pos", "val") [writeS]
    "arr" + "pos" *<-8 "val";;
    Return 0
  end with bfunction "inc"("arr", "len", "i", "tmp") [incS]
    "i" <- 0;;

    [Al arr,
      PRE[V] array8 arr (V "arr") * [| V "len" = length arr |] * [| goodSize (length arr) |]
        * [| (V "i" <= $(length arr))%word |]
      POST[_] Ex arr', array8 arr' (V "arr") * [| length arr' = length arr |]
        * [| forall j, (j < wordToNat (V "i"))%nat -> Array8.selN arr' j = Array8.selN arr j |]
        * [| forall j, (j >= wordToNat (V "i"))%nat -> Array8.selN arr' j = inc1 (Array8.selN arr j) |] ]
    While ("i" < "len") {
      "tmp" <-*8 "arr" + "i";;
      "tmp" <- "tmp" + 1;;
      "arr" + "i" *<-8 "tmp";;
      "i" <- "i" + 1
    };;

    Return 0
  end with bfunction "sum"("arr", "len", "i", "acc", "tmp") [sumS]
    "i" <- 0;;
    "acc" <- 0;;

    [Al done, Al rem,
      PRE[V] array8 (done ++ rem) (V "arr") * [| V "len" = length (done ++ rem) |]
        * [| goodSize (length (done ++ rem)) |] * [| V "i" = length done |]
      POST[R] array8 (done ++ rem) (V "arr") * [| R = V "acc" ^+ sum rem |] ]
    While ("i" < "len") {
      "tmp" <-*8 "arr" + "i";;
      "acc" <- "acc" + "tmp";;
      "i" <- "i" + 1
    };;

    Return "acc"
  end
}}.

Hint Rewrite roundTrip_0 : N.

Lemma zero_le : forall w : W, natToW 0 <= w.
  intros; nomega.
Qed.

Hint Immediate zero_le.

Lemma length_upd' : forall v bs p,
  length (Array8.updN bs p v) = length bs.
  induction bs; simpl; intuition.
  destruct p; simpl; intuition.
Qed.

Lemma length_upd : forall p v bs,
  length (Array8.upd bs p v) = length bs.
  intros; apply length_upd'.
Qed.

Hint Rewrite length_upd : sepFormula.

Lemma next' : forall (i : W),
  (exists len' : W, (wordToNat i < wordToNat len')%nat)
  -> wordToNat (i ^+ $(1)) = wordToNat i + 1.
  destruct 1; erewrite next; eauto.
  instantiate (1 := x); nomega.
Qed.

Hint Rewrite next' using (eexists; eassumption) : N.

Lemma next : forall (i : W),
  (exists len' : W, i < len')
  -> wordToNat (i ^+ $(1)) = wordToNat i + 1.
  destruct 1; eapply next'; eauto.
  pre_nomega; eauto.
Qed.

Hint Rewrite next using (eexists; eassumption) : sepFormula.

Lemma increment : forall (i len len' : W),
  i < len
  -> len = len'
  -> i ^+ $1 <= len'.
  intros; subst; pre_nomega; nomega.
Qed.

Hint Immediate increment.

Lemma wordToNat_eq : forall sz (u v : word sz),
  wordToNat u = wordToNat v
  -> u = v.
  intros; apply (f_equal (@natToWord sz)) in H;
    repeat rewrite natToWord_wordToNat in H; auto.
Qed.

Lemma squeeze : forall (len i len' : W),
  len <= i
  -> len = len'
  -> i <= len'
  -> len' = i.
  intros; subst; apply wordToNat_eq; nomega.
Qed.

Lemma inc_nil : inc nil = nil.
  auto.
Qed.

Hint Rewrite inc_nil app_nil_r : sepFormula.
Hint Rewrite wordToNat_natToWord_idempotent using assumption : sepFormula.

Lemma determine_inc : forall arr arr',
  length arr' = length arr
  -> (forall j, Array8.selN arr' j = inc1 (Array8.selN arr j))
  -> arr' = inc arr.
  induction arr; destruct arr'; simpl; intuition; f_equal.
  apply (H0 O).
  apply IHarr; auto.
  intro j; apply (H0 (S j)).
Qed.

Lemma selN_updN_eq : forall v ls p,
  (p < length ls)%nat
  -> Array8.selN (Array8.updN ls p v) p = v.
  induction ls; simpl; intuition.
  destruct p; simpl; intuition.
Qed.

Lemma selN_updN_ne : forall v ls p p',
  (p < length ls)%nat
  -> p <> p'
  -> Array8.selN (Array8.updN ls p v) p' = Array8.selN ls p'.
  induction ls; simpl; intuition.
  destruct p, p'; simpl; intuition.
Qed.

Lemma selN_upd_eq : forall v ls p,
  goodSize (length ls)
  -> p < natToW (length ls)
  -> Array8.selN (Array8.upd ls p v) (wordToNat p) = v.
  unfold Array8.upd; intros; apply selN_updN_eq; nomega.
Qed.

Lemma selN_upd_ne : forall v ls p p',
  goodSize (length ls)
  -> p < natToW (length ls)
  -> wordToNat p <> p'
  -> Array8.selN (Array8.upd ls p v) p' = Array8.selN ls p'.
  unfold Array8.upd; intros; apply selN_updN_ne; auto; nomega.
Qed.

Hint Resolve selN_upd_ne selN_upd_eq.

Hint Extern 1 (not (@eq nat _ _)) => omega.
Hint Extern 1 (_ < _) => congruence.

Lemma selN_oob : forall ls i,
  (i >= length ls)%nat
  -> Array8.selN ls i = wzero _.
  induction ls; simpl; intuition.
  destruct i; simpl; intuition.
Qed.

Lemma final_bound : forall (len i : W) len' j,
  goodSize len'
  -> len <= i
  -> len = natToW len'
  -> i <= natToW len'
  -> (j >= wordToNat i)%nat
  -> (j >= len')%nat.
  intros.
  assert (natToW len' = i) by eauto using squeeze.
  subst.
  rewrite wordToNat_natToWord_idempotent in H3; auto.
Qed.

Hint Resolve final_bound.

Lemma reveal_middle' : forall (ls1 ls2 : list B),
  (length ls1 < length (ls1 ++ ls2))%nat
  -> exists x, exists ls2', ls2 = x :: ls2'.
  intros; rewrite app_length in *.
  assert (length ls2 <> 0) by omega.
  destruct ls2; simpl in *; intuition eauto.
Qed.

Lemma reveal_middle : forall (ls1 ls2 : list B) i len,
  i < len
  -> i = natToW (length ls1)
  -> len = natToW (length (ls1 ++ ls2))
  -> goodSize (length (ls1 ++ ls2))
  -> exists x, exists ls2', ls2 = x :: ls2'.
  intros; subst.
  eapply reveal_middle'.
  instantiate (1 := ls1).
  rewrite app_length in *.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent in H.
  rewrite wordToNat_natToWord_idempotent in H; assumption.
  Transparent goodSize.
  red in H2.
  generalize dependent (Npow2 32); intros.
  nomega.
  Opaque goodSize.
Qed.

Hint Rewrite DepList.pf_list_simpl : sepFormula.

Lemma length_addendum : forall A (x : A) ls,
  length (ls ++ x :: nil) = length ls + 1.
  intros; rewrite app_length; auto.
Qed.

Hint Rewrite length_addendum : sepFormula.

Lemma sum_cons' : forall acc1 bs acc2,
  fold_left (fun n b => n ^+ BtoW b) bs (acc1 ^+ acc2) = acc1 ^+ fold_left (fun n b => n ^+ BtoW b) bs acc2.
  induction bs; simpl; intuition idtac.
  rewrite <- wplus_assoc.
  apply IHbs.
Qed.

Lemma sum_cons : forall b bs,
  sum (b :: bs) = BtoW b ^+ sum bs.
  unfold sum; simpl.
  intros.
  rewrite wplus_comm; apply sum_cons'.
Qed.

Hint Rewrite sum_cons : sepFormula.

Lemma selN_middle : forall post mid pre,
  Array8.selN (pre ++ mid :: post) (length pre) = mid.
  induction pre; simpl; intuition.
Qed.

Lemma sel_middle : forall i pre mid post,
  i = natToW (length pre)
  -> goodSize (length pre)
  -> Array8.sel (pre ++ mid :: post) i = mid.
  unfold Array8.sel; intros; subst.
  autorewrite with N.
  apply selN_middle.
Qed.

Hint Rewrite sel_middle using solve [ eauto 1 ] : sepFormula.

Lemma goodSize_split : forall A (ls1 ls2 : list A),
  goodSize (length (ls1 ++ ls2))
  -> goodSize (length ls1).
  intros; rewrite app_length in *; eapply goodSize_weaken; eauto.
Qed.

Hint Immediate goodSize_split.

Lemma all_done : forall len i A (done rem : list A),
  len <= i
  -> len = natToW (length (done ++ rem))
  -> i = natToW (length done)
  -> goodSize (length (done ++ rem))
  -> rem = nil.
  intros; subst.
  rewrite app_length in *.
  pre_nomega.
  assert (goodSize (length done)); eauto.
  rewrite wordToNat_natToWord_idempotent in *; eauto.
  rewrite wordToNat_natToWord_idempotent in *; eauto.
  destruct rem; simpl in *; auto; omega.
Qed.

Lemma sum_nil : sum nil = $0.
  auto.
Qed.

Hint Rewrite sum_nil : sepFormula.

Ltac useHyp := match goal with
                 | [ H : forall j : nat, _ |- _ ] => rewrite H by omega
               end.

Ltac finish :=
  match goal with
    | [ |- _ ^+ _ <= _ ] => eauto
    | [ |- sel _ "len" = natToW (length (?X ++ _))%nat ] => equate X (@nil B); simpl;
      eauto; reflexivity || words
    | [ |- himp _ (array8 ?A _) (array8 ?B _) ] =>
      replace B with A by eauto using determine_inc; reflexivity
    | [ H : sel _ "i" = _ |- _ ^+ natToW 1 = natToW (length _ + 1) ] => solve [ rewrite H; descend ]
    | [ _ : goodSize (length (_ ++ ?X)) |- _ ] => assert (X = nil) by eauto using all_done; subst;
      autorewrite with sepFormula; words
    | _ => solve [ useHyp; auto ]
    | _ => solve [ rewrite selN_oob; eauto ]
    | [ H : (?N >= ?M)%nat |- _ ] => destruct (eq_nat_dec N M); subst;
      useHyp; auto; rewrite selN_upd_ne; auto
    | _ => eauto; reflexivity || words
  end.

Ltac t :=
  try match goal with
        | [ |- forall stn_st specs, interp _ _ -> interp _ _ ] =>
          match goal with
            | [ |- context[LvMem8] ] => post; evaluate auto_ext;
              match goal with
                | [ H : goodSize (length (?done ++ _)) |- _ ] =>
                  let Ho := fresh in
                    generalize H; intro Ho; eapply reveal_middle in Ho; eauto; destruct Ho as [ mid [ rem ] ]; subst;
                      exists (done ++ mid :: nil); exists rem
              end
          end
      end; sep_auto; finish.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
