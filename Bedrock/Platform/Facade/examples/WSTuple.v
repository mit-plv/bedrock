Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Arrays8.
Require Import Bedrock.Platform.Facade.examples.ByteString.


Inductive nonempty (ws : WSTupl) : Prop :=
| Nonempty : forall len : W, len <> $0 -> wordToNat len = length ws -> nonempty ws.
Hint Constructors nonempty.

Module Type ADT.
  Parameter wstuple : WSTupl -> W -> HProp.
  Parameter wstuple' : WSTupl -> W -> HProp.
  Parameter wsitem : WS -> W -> W -> HProp.

  Axiom wstuple_fwd : forall ws p, wstuple ws p ===> wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |].
  Axiom wstuple_bwd : forall ws p, wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |] ===> wstuple ws p.

  Axiom wstuple'_nil_fwd : forall p, wstuple' nil p ===> Emp.
  Axiom wstuple'_word_fwd : forall w ws' p, wstuple' (WSWord w :: ws') p ===> (p ==*> $0, w) * wstuple' ws' (p ^+ $8).
  Axiom wstuple'_bytes_fwd : forall capacity bs ws' p, wstuple' (WSBytes capacity bs :: ws') p ===> Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8).

  Axiom wstuple'_nonzero_fwd : forall ws p,
      nonempty ws
      -> wstuple' ws p ===> Ex w, Ex ws', Ex tag, Ex sp,
           [| ws = w :: ws' |] * (p ==*> tag, sp) * wsitem w tag sp * wstuple' ws' (p ^+ $8).
  Axiom wsitem_word_fwd : forall w tag sp,
      tag = $0
      -> wsitem w tag sp ===> [| w = WSWord sp |].
  Axiom wsitem_bytes_fwd : forall w tag sp,
      tag <> $0
      -> wsitem w tag sp ===> Ex capacity, Ex bs, [| w = WSBytes capacity bs |] * bytes capacity bs sp.

  Axiom wstuple'_nil_bwd : forall p, Emp ===> wstuple' nil p.
  Axiom wstuple'_word_bwd : forall w ws' p, (p ==*> $0, w) * wstuple' ws' (p ^+ $8) ===> wstuple' (WSWord w :: ws') p.
  Axiom wstuple'_bytes_bwd : forall capacity bs ws' p, Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8) ===> wstuple' (WSBytes capacity bs :: ws') p.
End ADT.

Module Import Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint wstuple' (ws : WSTupl) (p : W) : HProp :=
    match ws with
    | nil => Emp
    | WSWord w :: ws' => (p ==*> $0, w) * wstuple' ws' (p ^+ $8)
    | WSBytes capacity bs :: ws' => Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8)
    end.

  Definition wstuple (ws : WSTupl) (p : W) : HProp :=
    wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |].

  Definition wsitem (w : WS) (tag p : W) :=
    match w with
    | WSWord w => [| tag = $0 |] * [| w = p |]
    | WSBytes capacity bs => [| tag = $1 |] * bytes capacity bs p
    end.

  Theorem wstuple_fwd : forall ws p, wstuple ws p ===> wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |].
  Proof.
    unfold wstuple; sepLemma.
  Qed.

  Theorem wstuple_bwd : forall ws p, wstuple' ws p * [| p <> 0 |] * [| freeable p (length ws * 2) |] ===> wstuple ws p.
  Proof.
    unfold wstuple; sepLemma.
  Qed.

  Theorem wstuple'_nil_fwd : forall p, wstuple' nil p ===> Emp.
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_word_fwd : forall w ws' p, wstuple' (WSWord w :: ws') p ===> (p ==*> $0, w) * wstuple' ws' (p ^+ $8).
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_nonzero_fwd : forall ws p,
      nonempty ws
      -> wstuple' ws p ===> Ex w, Ex ws', Ex tag, Ex sp,
           [| ws = w :: ws' |] * (p ==*> tag, sp) * wsitem w tag sp * wstuple' ws' (p ^+ $8).
  Proof.
    destruct 1.
    destruct ws; simpl; intuition.
    apply (f_equal (natToWord 32)) in H0.
    rewrite natToWord_wordToNat in H0.
    tauto.
    destruct w.
    sepLemma.
    simpl.
    sepLemma.
    sepLemma.
    simpl.
    sepLemma.
  Qed.

  Theorem wsitem_word_fwd : forall w tag sp,
      tag = $0
      -> wsitem w tag sp ===> [| w = WSWord sp |].
  Proof.
    destruct w; sepLemma; discriminate.
  Qed.

  Theorem wsitem_bytes_fwd : forall w tag sp,
      tag <> $0
      -> wsitem w tag sp ===> Ex capacity, Ex bs, [| w = WSBytes capacity bs |] * bytes capacity bs sp.
  Proof.
    destruct w; sepLemma; discriminate.
  Qed.

  Theorem wstuple'_bytes_fwd : forall capacity bs ws' p, wstuple' (WSBytes capacity bs :: ws') p ===> Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8).
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_nil_bwd : forall p, Emp ===> wstuple' nil p.
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_word_bwd : forall w ws' p, (p ==*> $0, w) * wstuple' ws' (p ^+ $8) ===> wstuple' (WSWord w :: ws') p.
  Proof.
    sepLemma.
  Qed.

  Theorem wstuple'_bytes_bwd : forall capacity bs ws' p, Ex sp, (p ==*> $1, sp) * bytes capacity bs sp * wstuple' ws' (p ^+ $8) ===> wstuple' (WSBytes capacity bs :: ws') p.
  Proof.
    sepLemma.
  Qed.
End Adt.

Export Adt.

Lemma expose_words : forall p len : W,
    len <> $0
    -> p =?> (wordToNat len * 2)
         ===> Ex w1, Ex w2, (p ==*> w1, w2) * (p ^+ $8) =?> (wordToNat (len ^- $1) * 2).
Proof.
  intros.
  case_eq (wordToNat len); intros.

  apply (f_equal (natToWord 32)) in H0.
  rewrite natToWord_wordToNat in H0.
  tauto.

  sepLemma.
  apply allocated_shift_base.
  words.
  rewrite wordToNat_wminus; auto.
  pre_nomega.
  change (wordToNat (natToW 1)) with 1.
  omega.
Qed.

Fixpoint zeroes (n : nat) : WSTupl :=
  match n with
  | O => nil
  | S n' => WSWord 0 :: zeroes n'
  end.

Lemma zeroes_nonzero_bwd : forall w p : W,
    w <> $0
    -> (p ==*> $0, $0) * wstuple' (zeroes (wordToNat (w ^- $1))) (p ^+ $8)
       ===> wstuple' (zeroes (wordToNat w)) p.
Proof.
  intros.
  rewrite wordToNat_wminus.
  change (wordToNat $1) with 1.
  case_eq (wordToNat w); intros.
  apply (f_equal (natToWord 32)) in H0.
  rewrite natToWord_wordToNat in H0.
  tauto.
  simpl.
  replace (n - 0) with n by omega.
  eapply Himp_trans; [ | apply wstuple'_word_bwd ].
  sepLemma.
  pre_nomega.
  change (wordToNat ($1)) with 1.
  case_eq (wordToNat w); intros.
  apply (f_equal (natToWord 32)) in H0.
  rewrite natToWord_wordToNat in H0.
  tauto.
  omega.
Qed.

Lemma allocated2 : forall base offset,
    (Ex v1, Ex v2, (base ^+ $ offset) =*> v1 * (base ^+ ($ offset ^+ $4)) =*> v2) ===> allocated base offset 2.
Proof.
  simpl.
  destruct offset; sepLemma.
  replace (S (S (S (S (S offset))))) with (S offset + 4) by omega.
  sepLemma.
Qed.

Lemma wtimes8 : forall n,
      natToW (n * 8) = natToW n ^* $8.
Proof.
  intros.
  replace (n * 8) with (8 * n) by omega.
  simpl.
  repeat rewrite natToW_plus.
  words.
Qed.

Opaque mult.

Lemma blob_absorb : forall (len tmpl self : W),
    (wordToNat len >= wordToNat tmpl)%nat
    -> tmpl <> $0
    -> (Ex v1, Ex v2, self =?> ((wordToNat len - wordToNat tmpl) * 2) * (self ^+ (len ^- tmpl) ^* $8) =*> v1 * (self ^+ (len ^- tmpl) ^* $8 ^+ $4) =*> v2)
    ===> self =?> ((wordToNat len - (wordToNat tmpl - 1)) * 2).
Proof.
  intros.
  eapply Himp_trans; [ | apply allocated_join with (len' := (wordToNat len - wordToNat tmpl) * 2) ].
  replace ((wordToNat len - (wordToNat tmpl - 1)) * 2 -
           (wordToNat len - wordToNat tmpl) * 2) with 2.
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply allocated2 ] ].
  sepLemma.
  replace (4 * ((wordToNat len - wordToNat tmpl) * 2))
          with ((wordToNat len - wordToNat tmpl) * 8) by omega.
  rewrite natToW_plus.
  rewrite <- wordToNat_wminus by nomega.
  rewrite wtimes8.
  unfold natToW.
  rewrite natToWord_wordToNat.
  replace (self ^+ ((len ^- tmpl) ^* $ (8) ^+ $ (4)))
    with (self ^+ (len ^- tmpl) ^* $ (8) ^+ $ (4)) by words.
  sepLemma.
  assert (wordToNat tmpl <> 0).
  intro.
  apply (f_equal (natToWord 32)) in H1.
  rewrite natToWord_wordToNat in H1.
  tauto.
  omega.
  pre_nomega.
  change (wordToNat $1) with 1.
  case_eq (wordToNat tmpl); intros.
  apply (f_equal (natToWord 32)) in H1.
  rewrite natToWord_wordToNat in H1.
  tauto.    
  omega.
Qed.

Definition hints : TacPackage.
  prepare (wstuple_fwd, wstuple'_nil_fwd, wstuple'_word_fwd, wstuple'_bytes_fwd,
           expose_words, wstuple'_nonzero_fwd, wsitem_word_fwd, wsitem_bytes_fwd)
          (wstuple_bwd, wstuple'_nil_bwd, wstuple'_word_bwd, wstuple'_bytes_bwd,
           zeroes_nonzero_bwd, blob_absorb).
Defined.

Definition newS := SPEC("extra_stack", "len") reserving 8
  PRE[V] [| wordToNat (V "len") >= 1 |]%nat * [| goodSize (wordToNat (V "len") * 2) |] * mallocHeap 0
  POST[R] wstuple (zeroes (wordToNat (V "len"))) R * mallocHeap 0.

Definition deleteS := SPEC("extra_stack", "self", "len") reserving 11
  Al ws,
  PRE[V] wstuple ws (V "self") * [| wordToNat (V "len") = length ws |] * mallocHeap 0
  POST[R] [| R = $0 |] * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "ByteString"!"delete" @ [ByteString.deleteS],
                           "ByteString"!"copy" @ [ByteString.copyS] ]]
  bmodule "WSTuple" {{
    (*bfunction "new"("extra_stack", "len", "tmp") [newS]
      "extra_stack" <- "len" * 2;;
      "extra_stack" <-- Call "malloc"!"malloc"(0, "extra_stack")
      [PRE[V, R] R =?> (wordToNat (V "len") * 2) * [| goodSize (wordToNat (V "len") * 2) |]
       POST[R'] [| R' = R |] * wstuple' (zeroes (wordToNat (V "len"))) R];;

      "tmp" <- "extra_stack";;
      [PRE[V] V "tmp" =?> (wordToNat (V "len") * 2) * [| goodSize (wordToNat (V "len") * 2) |]
       POST[R] [| R = V "extra_stack" |] * wstuple' (zeroes (wordToNat (V "len"))) (V "tmp")]
      While ("len" <> 0) {
        "tmp" *<- 0;;
        "tmp"+4 *<- 0;;
        "tmp" <- "tmp" + 8;;
        "len" <- "len" - 1
      };;

      Return "extra_stack"
    end

    with*) bfunction "delete"("extra_stack", "self", "len", "tmp", "tmpl") [deleteS]
      "tmp" <- "self";;
      "tmpl" <- "len";;
      [Al ws,
       PRE[V] wstuple' ws (V "tmp")
              * [| wordToNat (V "tmpl") = length ws |]
              * V "self" =?> ((wordToNat (V "len") - wordToNat (V "tmpl")) * 2)
              * [| wordToNat (V "len") >= wordToNat (V "tmpl") |]%nat
              * [| V "tmp" = V "self" ^+ ((V "len" ^- V "tmpl") ^* $8) |]
              * [| V "self" <> $0 |] * [| freeable (V "self") (wordToNat (V "len") * 2) |]
              * mallocHeap 0
       POST[R] [| R = $0 |] * mallocHeap 0 ]
      While ("tmpl" <> 0) {
        Assert [Al ws,
                PRE[V] wstuple' ws (V "tmp")
                       * [| wordToNat (V "tmpl") = length ws |]
                       * V "self" =?> ((wordToNat (V "len") - wordToNat (V "tmpl")) * 2)
                       * [| wordToNat (V "len") >= wordToNat (V "tmpl") |]%nat
                       * [| V "tmp" = V "self" ^+ ((V "len" ^- V "tmpl") ^* $8) |]
                       * [| V "self" <> $0 |] * [| freeable (V "self") (wordToNat (V "len") * 2) |]
                       * [| nonempty ws |] * [| V "tmpl" <> 0 |]
                       * mallocHeap 0
                POST[R] [| R = $0 |] * mallocHeap 0 ];;

        "extra_stack" <-* "tmp";;
        If ("extra_stack" = 0) {
          Skip
        } else {
          "extra_stack" <-* "tmp"+4;;
          Call "ByteString"!"delete"("extra_stack", "extra_stack")
          [Al ws,
           PRE[V] wstuple' ws (V "tmp" ^+ $8)
                  * [| wordToNat (V "tmpl" ^- $1) = length ws |]
                  * V "self" =?> ((wordToNat (V "len") - wordToNat (V "tmpl" ^- $1)) * 2)
                  * [| wordToNat (V "len") >= wordToNat (V "tmpl" ^- $1) |]%nat
                  * [| V "tmp" ^+ $8 = V "self" ^+ ((V "len" ^- (V "tmpl" ^- $1)) ^* $8) |]
                  * [| V "self" <> $0 |] * [| freeable (V "self") (wordToNat (V "len") * 2) |]
                  * mallocHeap 0
           POST[R] [| R = $0 |] * mallocHeap 0 ]
         };;
        "tmp" <- "tmp" + 8;;
        "tmpl" <- "tmpl" - 1
      };;

      "len" <- "len" * 2;;
      Call "malloc"!"free"(0, "self", "len")
      [PRE[_] Emp
       POST[R] [| R = $0 |] ];;
      Return 0
    end
  }}.

Lemma two_le : forall w : W,
    (wordToNat w >= 1)%nat
    -> goodSize (wordToNat w * 2)
    -> $2 <= w ^* $2.
Proof.
  intros.
  pre_nomega.
  rewrite wordToNat_wmult.
  change (wordToNat $2) with 2.
  omega.
  assumption.
Qed.

Hint Immediate two_le.

Lemma times2 : forall w : W,
    goodSize (wordToNat w * 2)
    -> wordToNat (w ^* $2) = wordToNat w * 2.
Proof.
  intros; pre_nomega.
  rewrite wordToNat_wmult; auto.
Qed.

Hint Rewrite times2 using assumption : sepFormula.

Lemma length_zeroes : forall n,
    length (zeroes n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Hint Rewrite length_zeroes : sepFormula.

Lemma goodSize_minus1 : forall w : W,
    goodSize (wordToNat w * 2)
    -> w <> $0
    -> goodSize (wordToNat (w ^- $1) * 2).
Proof.
  intros.
  eapply goodSize_weaken; eauto.
  rewrite wordToNat_wminus.
  change (wordToNat ($1)) with 1.
  omega.
  pre_nomega.
  case_eq (wordToNat w); intros.
  apply (f_equal (natToWord 32)) in H1.
  rewrite natToWord_wordToNat in H1.
  tauto.
  change (wordToNat ($1)) with 1.
  omega.
Qed.

Hint Immediate goodSize_minus1.

Lemma zeroes_zero_bwd : forall w p : W,
    w = $0
    -> p =?> (wordToNat w * 2) ===> wstuple' (zeroes (wordToNat w)) p.
Proof.
  intros; subst.
  change (wordToNat $0) with 0.
  simpl.
  apply wstuple'_nil_bwd.
Qed.

Hint Extern 1 (himp _ _ _) => apply zeroes_zero_bwd.

Lemma goodlength_godown : forall (w : W) n,
    wordToNat w = S n
    -> wordToNat (w ^- $1) = n.
Proof.
  intros.
  rewrite wordToNat_wminus.
  change (wordToNat $1) with 1.
  omega.
  pre_nomega.
  change (wordToNat $1) with 1.
  omega.
Qed.

Hint Immediate goodlength_godown.

Lemma geq_godown : forall len (tmpl : W) n,
    (len >= wordToNat tmpl)%nat
    -> wordToNat tmpl = S n
    -> (len >= wordToNat (tmpl ^- $1))%nat.
Proof.
  intros.
  rewrite H0 in *.
  rewrite wordToNat_wminus.
  change (wordToNat $1) with 1.
  omega.
  pre_nomega.
  change (wordToNat $1) with 1.
  omega.
Qed.

Hint Immediate geq_godown.

Hint Extern 1 (?x ^+ _ = _) =>
  match goal with
  | [ H : x = _ |- _ ] => rewrite H; words
  end.

Lemma minus_positive : forall w : W,
    w <> $0
    -> wordToNat (w ^- $1) = wordToNat w - 1.
Proof.
  intros; rewrite wordToNat_wminus; auto.
  pre_nomega.
  change (wordToNat $1) with 1.
  case_eq (wordToNat w); intros.
  apply (f_equal (natToWord 32)) in H0.
  rewrite natToWord_wordToNat in H0.
  tauto.
  omega.
Qed.

Hint Rewrite minus_positive using assumption : sepFormula.

Inductive containsAllocated : HProp -> nat -> Prop :=
| CAlBase : forall len p, containsAllocated (p =?> len)%Sep len
| CAlLeft : forall P Q len, containsAllocated P len
  -> containsAllocated (SEP.ST.star P Q) len
| CAlRight : forall P Q len, containsAllocated Q len
  -> containsAllocated (SEP.ST.star P Q) len.

Hint Constructors containsAllocated.

Require Import Bedrock.Platform.MoreArrays.

Lemma containsAllocated_containsArray : forall P len,
    containsAllocated P len
    -> exists Q, P ===> Ex ws, Ex p, array ws p * [| length ws = len |] * Q.
Proof.
  induction 1.

  exists Emp%Sep.
  eapply Himp_trans; [ apply allocate_array; auto | ].
  sepLemma.

  destruct IHcontainsAllocated.
  exists (x * Q)%Sep.
  eapply Himp_trans; [ eapply Himp_star_frame; [ apply H0 | apply Himp_refl ] | ].
  clear H.
  sepLemma.

  destruct IHcontainsAllocated.
  exists (x * P)%Sep.
  eapply Himp_trans; [ eapply Himp_star_frame; [ apply Himp_refl | apply H0 ] | ].
  clear H.
  sepLemma.
Qed.

Lemma use_Himp : forall cs P arg P',
    interp cs (![P] arg)
    -> P ===> P'
    -> interp cs (![P'] arg).
Proof.
  intros.
  rewrite sepFormula_eq in *.
  destruct arg.
  unfold Himp, himp in H0.
  eapply Imply_E.
  apply H0.
  assumption.
Qed.

Theorem containsAllocated_goodSize : forall cs P stn st len,
    interp cs (![P] (stn, st))
    -> containsAllocated P len
    -> goodSize len.
Proof.
  intros.
  apply containsAllocated_containsArray in H0.
  destruct H0.
  eapply use_Himp in H0; eauto.
  evaluate auto_ext.
  fold (@length W) in *.
  subst.
  eapply containsArray_goodSize; eauto.
Qed.

Hint Rewrite times2
     using eapply goodSize_weaken; [ eapply containsAllocated_goodSize; [ eassumption | eauto ] | match goal with
                                                                                                  | [ H : _ = natToW 0 |- _ ] => rewrite H; change (wordToNat (natToW 0)) with 0; omega
                                                                                                  end ] : sepFormula.

Lemma tmpl_zero : forall tmpl n,
    tmpl = natToW 0
    -> n - wordToNat tmpl = n.
Proof.
  intros; subst.
  change (wordToNat (natToW 0)) with 0.
  omega.
Qed.

Hint Rewrite tmpl_zero using assumption : sepFormula.

Lemma wstuple_delete : forall specs ws tmp tmpl,
    wordToNat tmpl = length ws
    -> tmpl = natToW 0
    -> himp specs (wstuple' ws tmp) (SEP.ST.emp W (settings * state)).
Proof.
  intros; subst.
  change (wordToNat (natToW 0)) with 0 in *.
  destruct ws; simpl in *; try discriminate.
  step hints.
Qed.

Hint Extern 1 (himp _ (wstuple' _ _) _ ) => eapply wstuple_delete; eassumption.

Ltac t := solve [ sep hints; eauto ].

Local Hint Extern 1 (@eq W _ _) => words.
Local Hint Extern 1 (freeable _ _) => congruence.
Hint Rewrite Minus.minus_diag : sepFormula.

Transparent mult.

Theorem ok : moduleOk m.
Proof.
  vcgen.

  (*t.
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
  t.*)

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
