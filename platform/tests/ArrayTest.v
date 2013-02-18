Require Import Arith AutoSep Malloc.


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

Definition testS := SPEC reserving 9
  PREonly[_] mallocHeap 0.

Inductive please_materialize (sz : nat) : Prop := PleaseMaterialize.
Hint Constructors please_materialize.

Definition array8_decomission (sz : nat) := array8.

Definition decomission_ok (sz : nat) (bs : list B) :=
  length bs = sz * 4.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS] ]]
  bmodule "array" {{
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
  end with bfunctionNoRet "test"("arr", "tmp") [testS]
    "arr" <-- Call "malloc"!"malloc"(0, 2)
    [PREonly[_, R] mallocHeap 0 * R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] ];;

    Note [please_materialize 2];;

    Assert [Al arr,
      PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
        * array8 arr (V "arr") * [| length arr = 8|] ];;

    "tmp" <- 0;;
    [Al arr,
      PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
        * array8 arr (V "arr") * [| length arr = 8 |] ]
    While ("tmp" < 8) {
      Assert [Al arr,
        PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
        * array8 arr (V "arr") * [| length arr = 8 |] * [| (V "tmp" < natToW (length arr))%word |] ];;

      "arr" + "tmp" *<-8 "tmp";;
      "tmp" <- "tmp" + 1
    };;

    Call "array"!"inc"("arr", 8)
    [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8 arr (V "arr") * [| length arr = 8 |] ];;

    "tmp" <-- Call "array"!"sum"("arr", 8)
    [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8 arr (V "arr") * [| length arr = 8 |] ];;

    Call "sys"!"printInt"("tmp")
    [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8 arr (V "arr") * [| length arr = 8 |] ];;

    Assert [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8_decomission 2 arr (V "arr") * [| decomission_ok 2 arr |] ];;

    Assert [PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * V "arr" =?> 2];;

    Call "malloc"!"free"(0, "arr", 2)
    [PREonly[_] Emp];;

    Call "sys"!"abort"()
    [PREonly[_] [| False |] ]
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

Lemma materialize_array8'' : forall p v,
  p =*> v ===> Ex b1, p =8> b1 * Ex b2, (p ^+ $1) =8> b2 * Ex b3, (p ^+ $2) =8> b3 * Ex b4, (p ^+ $3) =8> b4.
  intros; hnf; unfold himp; intros.
  unfold ptsto32, ptsto8, hptsto.
  apply injL; intuition.
  propxFo.
  unfold smem_get_word, H.footprint_w in *.
  
  Require Import Bootstrap.

  repeat match type of H0 with
           | match ?E with None => _ | _ => _ end = _ => case_eq E; intros;
             match goal with
               | [ H : _ = _ |- _ ] => rewrite H in *
             end; try discriminate
         end.
  do 4 esplit.
  apply split_put_clear; [ apply split_a_semp_a | apply H ].
  Local Hint Resolve get_put_eq get_put_ne get_emp.
  intuition eauto.
  rewrite get_put_ne; auto.
  do 4 esplit.
  apply split_put_clear; [ apply split_a_semp_a | ].
  rewrite get_clear_ne; apply H2 || W_neq.
  intuition eauto.
  rewrite get_put_ne; auto.
  do 4 esplit.
  apply split_put_clear; [ apply split_a_semp_a | ].
  rewrite get_clear_ne.
  rewrite get_clear_ne; try apply H3.
  W_neq.
  W_neq.
  intuition eauto.
  rewrite get_put_ne; auto.
  do 2 esplit.
  rewrite get_clear_ne.
  rewrite get_clear_ne.
  rewrite get_clear_ne; try apply H4.
  W_neq.
  W_neq.
  W_neq.
  intros.
  destruct (weq p' (p ^+ $2)); subst.
  apply get_clear_eq.
  rewrite get_clear_ne by auto.
  destruct (weq p' (p ^+ $1)); subst.
  apply get_clear_eq.
  rewrite get_clear_ne by auto.
  destruct (weq p' p); subst.
  apply get_clear_eq.
  rewrite get_clear_ne; eauto.
Qed.

Lemma materialize_array8' : forall p sz offset,
  allocated p offset sz ===> Ex bs, array8 bs (p ^+ $(offset)) * [| (length bs = sz * 4)%nat |].
  induction sz; simpl; intuition.
  
  sepLemma.
  instantiate (1 := nil); auto.
  sepLemma.

  sepLemmaLhsOnly.
  destruct offset.
  etransitivity; [ eapply himp_star_frame; [ apply IHsz | apply materialize_array8'' ] | ].
  sepLemmaLhsOnly.
  fold (@length B) in *.
  apply himp_ex_c; exists (x3 :: x2 :: x1 :: x0 :: x4).
  sepLemma.
  etransitivity; [ eapply himp_star_frame; [ apply IHsz | apply materialize_array8'' ] | ].
  sepLemmaLhsOnly.
  fold (@length B) in *.
  apply himp_ex_c; exists (x3 :: x2 :: x1 :: x0 :: x4).
  sepLemma.
  match goal with
    | [ |- himp _ (array8 _ ?X) (array8 _ ?Y) ] => replace Y with X; try reflexivity
  end.
  rewrite (natToW_S (S (S (S (S offset))))).
  rewrite (natToW_S (S (S (S offset)))).
  rewrite (natToW_S (S (S offset))).
  rewrite (natToW_S (S offset)).
  rewrite (natToW_S offset).
  words.
Qed.

Theorem materialize_array8 : forall p sz,
  p =?> sz ===> Ex bs, array8 bs p * [| (length bs = sz * 4)%nat |].
  intros; eapply Himp_trans; [ apply materialize_array8' | ].
  replace (p ^+ $0) with p by words.
  apply Himp_refl.
Qed.

Lemma decomission_array8'' : forall p b1 b2 b3 b4,
  (p =8> b1 * (p ^+ $1) =8> b2 * (p ^+ $2) =8> b3 * (p ^+ $3) =8> b4) ===> Ex w, p =*> w.
  intros; hnf; unfold himp; intros.
  unfold ptsto32, ptsto8, hptsto.
  repeat ((apply existsL; intro) || (apply andL; (apply injL; intro) || (apply swap; apply injL; intro))).
  apply injL; intuition.
  propxFo.
  do 2 esplit.
  unfold smem_get_word, H.footprint_w.
  repeat (erewrite split_smem_get; [ | | eauto ]).
  eauto.
  eauto.
  eapply split_assoc.
  apply split_comm; eauto.
  eauto.
  eapply split_assoc.
  apply split_comm; eauto.
  eapply split_assoc.
  apply split_comm; eauto.
  eauto.
  eapply split_assoc.
  apply split_comm; eauto.
  eapply split_assoc.
  apply split_comm; eauto.
  apply split_comm; eauto.
  intuition idtac.
  unfold split in *; intuition subst.
  repeat rewrite join_None; eauto.
Qed.

Lemma decomission_array8' : forall p sz bs offset sz',
  length bs = sz' * 4
  -> (sz' < sz)%nat
  -> array8 bs (p ^+ $(offset)) ===> allocated p offset sz'.
  induction sz; simpl; intuition.

  destruct bs; simpl in *.
  destruct sz'; simpl in *; try discriminate.
  sepLemma.

  destruct sz'; simpl in *; try discriminate.
  do 3 (destruct bs; simpl in *; try discriminate).
  replace (p ^+ $(offset) ^+ $1 ^+ $1 ^+ $1) with (p ^+ $(offset) ^+ $3) by words.
  replace (p ^+ $(offset) ^+ $1 ^+ $1) with (p ^+ $(offset) ^+ $2) by words.

  Lemma pull_out : forall P Q R S T,
    P * (Q * (R * (S * T))) ===> (P * Q * R * S) * T.
    sepLemma.
  Qed.

  eapply Himp_trans; [ apply pull_out | ].
  apply Himp_star_frame.
  eapply Himp_trans; [ apply decomission_array8'' | ].
  destruct offset; sepLemma.
  eapply Himp_trans; [ | apply IHsz ]; auto.
  match goal with
    | [ |- array8 _ ?X ===> array8 _ ?Y ] => replace Y with X; try apply Himp_refl
  end.
  change ($ (S (S (S (S offset))))) with (natToW (S (S (S (S offset))))).
  rewrite (natToW_S (S (S (S offset)))).
  rewrite (natToW_S (S (S offset))).
  rewrite (natToW_S (S offset)).
  rewrite (natToW_S offset).
  unfold natToW.
  W_eq.
  congruence.
Qed.

Lemma decomission_array8 : forall p bs sz,
  length bs = sz * 4
  -> array8 bs p ===> p =?> sz.
  intros; eapply Himp_trans; [ | eapply decomission_array8' ].
  replace (p ^+ $0) with p by words; apply Himp_refl.
  auto.
  constructor.
Qed.

Theorem materialize_array8_tagged : forall p sz,
  please_materialize sz
  -> p =?> sz ===> Ex bs, array8 bs p * [| (length bs = sz * 4)%nat |].
  intros; apply materialize_array8.
Qed.

Lemma decomission_array8_tagged : forall p bs sz,
  decomission_ok sz bs
  -> array8_decomission sz bs p ===> p =?> sz.
  intros; apply decomission_array8; auto.
Qed.

Definition hints : TacPackage.
  prepare (materialize_array8_tagged, decomission_array8_tagged) tt.
Defined.

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

Ltac t := solve [
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
      end; sep hints; finish ].

Opaque array8 allocated.

Lemma length_inc : forall ls, length (inc ls) = length ls.
  intros; apply map_length.
Qed.

Hint Rewrite length_inc : sepFormula.

Lemma goodSize8 : forall n, n = 8
  -> goodSize n.
  intros; subst; auto.
Qed.

Hint Immediate goodSize8.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
