Require Import AutoSep Bootstrap Malloc Buffers XmlLex XmlLang Arrays8.


Module Type HIDE.
  Parameter heapSize4 : N -> N.
  Axiom heapSize4_eq : forall n, heapSize4 n = (n * 4)%N.

  Parameter to_nat : N -> nat.
  Axiom to_nat_eq : to_nat = N.to_nat.
End HIDE.

Module Hide : HIDE.
  Definition heapSize4 n := (n * 4)%N.
  Theorem heapSize4_eq : forall n, heapSize4 n = (n * 4)%N.
    auto.
  Qed.

  Definition to_nat := N.to_nat.
  Theorem to_nat_eq : to_nat = N.to_nat.
    auto.
  Qed.
End Hide.


Module Type S.
  Parameter pr : program.
  Axiom wellFormed : wf (Pattern pr).
  Axiom inScope : freeVar (Pattern pr) (Output pr).
  Axiom notTooGreedy : (reserved pr <= 44)%nat.

  Parameter inbuf_size : N.
  Axiom inbuf_size_lower : (inbuf_size >= 2)%N.
  Axiom inbuf_size_upper : (inbuf_size * 4 < Npow2 32)%N.

  Parameter heapSize : N.
End S.

Module Make(M : S).
Import M.

Definition mainS := SPEC reserving 49
  PREonly[_] mallocHeap 0.

Definition bsize := nat_of_N (inbuf_size * 4)%N.

Inductive unfold_here := UnfoldHere.
Local Hint Constructors unfold_here.

Definition hints : TacPackage.
  prepare buffer_split_tagged tt.
Defined.

Definition m0 := bimport [[ "buffers"!"bmalloc" @ [bmallocS], "sys"!"abort" @ [abortS],
                            "sys"!"read" @ [Sys.readS], "xml_prog"!"main" @ [XmlLang.mainS pr] ]]
  bmodule "xml_driver" {{
    bfunctionNoRet "main"("inbuf", "len") [mainS]
      "inbuf" <-- Call "buffers"!"bmalloc"(inbuf_size)
      [PREonly[_, R] R =?>8 bsize * mallocHeap 0];;

      "len" <-- Call "sys"!"read"(0, "inbuf", bsize)
      [PREonly[V] V "inbuf" =?>8 bsize * mallocHeap 0];;

      If ("len" > bsize) {
        Call "sys"!"abort"()
        [PREonly[_] [| False |] ]
      } else {
        Assert [PREonly[V] buffer_splitAt (wordToNat (V "len")) (V "inbuf") bsize * mallocHeap 0
          * [| wordToNat (V "len") <= bsize |]%nat ];;

        Assert [PREonly[V] V "inbuf" =?>8 wordToNat (V "len") * mallocHeap 0 ];;

        Note [unfold_here];;

        Call "xml_prog"!"main"("inbuf", "len")
        [PREonly[_] Emp];;

        Call "sys"!"abort"()
        [PREonly[_] [| False |] ]
      }
    end
  }}.

Lemma inbuf_size_lower'' : (inbuf_size < Npow2 32)%N.
  eapply Nlt_trans; [ | apply inbuf_size_upper ].
  specialize inbuf_size_lower; intros.
  pre_nomega.
  rewrite N2Nat.inj_mul.
  simpl.
  generalize dependent (N.to_nat inbuf_size); intros.
  change (Pos.to_nat 2) with 2 in *.
  change (Pos.to_nat 4) with 4.
  omega.
Qed.

Lemma inbuf_size_lower' : natToW 2 <= NToW inbuf_size.
  unfold NToW.
  rewrite NToWord_nat.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent.
  change (wordToNat (natToW 2)) with (nat_of_N 2).
  apply Nge_out.
  apply inbuf_size_lower.
  rewrite N2Nat.id.
  apply inbuf_size_lower''.
Qed.

Local Hint Immediate inbuf_size_lower'.

Lemma bsize_in : (wordToNat (NToW inbuf_size) * 4) = bsize.
  unfold NToW, bsize.
  rewrite NToWord_nat.
  rewrite N2Nat.inj_mul.
  rewrite wordToNat_natToWord_idempotent.
  auto.
  rewrite N2Nat.id.
  apply inbuf_size_lower''.
Qed.

Lemma bsize_roundTrip : wordToNat (natToW bsize) = bsize.
  apply wordToNat_natToWord_idempotent.
  unfold bsize.
  rewrite N2Nat.id.
  apply inbuf_size_upper.
Qed.

Hint Rewrite bsize_in bsize_roundTrip : sepFormula.
Hint Rewrite bsize_roundTrip : N.

Ltac t :=
  try match goal with
        | [ |- context[unfold_here] ] => unfold buffer; generalize notTooGreedy
      end; sep hints; auto; nomega.

Theorem ok0 : moduleOk m0.
  vcgen; abstract t.
Qed.

Section boot.
  Definition heapSize' := Hide.to_nat heapSize.

  Hypothesis heapSizeLowerBound : (3 <= heapSize)%N.

  Let heapSizeLowerBound' : (3 <= heapSize')%nat.
    intros; unfold heapSize'; rewrite Hide.to_nat_eq.
    assert (heapSize >= 3)%N by (apply N.le_ge; apply heapSizeLowerBound); nomega.
  Qed.

  Definition size := heapSize' + 50 + 0.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize' * 4).
    goodSize.
  Qed.

  Lemma heapSizeLowerBound'' : natToW 3 <= NToW heapSize.
    hnf; intros.
    red in H.
    pre_nomega.
    rewrite wordToNat_natToWord_idempotent in H by reflexivity.
    unfold heapSize' in *.
    rewrite Hide.to_nat_eq in *.
    unfold NToW in *.
    rewrite NToWord_nat in *.
    rewrite wordToNat_natToWord_idempotent in H.
    omega.
    rewrite N2Nat.id.
    eapply goodSize_weaken in mem_size.
    2: instantiate (1 := N.to_nat heapSize); unfold size.
    Transparent goodSize.
    unfold goodSize in *.
    rewrite N2Nat.id in *.
    assumption.
    unfold heapSize'.
    rewrite Hide.to_nat_eq.
    omega.
  Qed.

  Hint Immediate heapSizeLowerBound''.

  Definition bootS := {|
    Reserved := 49;
    Formals := nil;
    Precondition := fun _ => st ~> ![ 0 =?> (heapSize' + 50 + 0) ] st
  |}.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "xml_driver"!"main" @ [mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%N;;

        Assert [PREonly[_] 0 =?> heapSize' ];;

        Call "malloc"!"init"(0, heapSize)
        [PREonly[_] mallocHeap 0];;

        Goto "xml_driver"!"main"
      end
    }}.

  Lemma bootstrap_Sp_nonzero : forall sp : W,
    sp = 0
    -> sp = (heapSize' * 4)%nat
    -> goodSize (heapSize' * 4)
    -> False.
    intros; eapply bootstrap_Sp_nonzero; try eassumption; eauto.
  Qed.

  Lemma bootstrap_Sp_freeable : forall sp : W,
    sp = (heapSize' * 4)%nat
    -> freeable sp 50.
    intros; eapply bootstrap_Sp_freeable; try eassumption; eauto.
  Qed.

  Lemma noWrap : noWrapAround 4 (wordToNat (NToW heapSize) - 1).
    intros.
    unfold NToW; rewrite NToWord_nat by auto.
    unfold heapSize' in *; rewrite Hide.to_nat_eq in *.
    rewrite wordToNat_natToWord_idempotent.
    apply noWrap; eauto.
    eapply goodSize_weaken.
    2: instantiate (1 := (heapSize' * 4)%nat).
    unfold heapSize'; rewrite Hide.to_nat_eq; auto.
    unfold heapSize'; rewrite Hide.to_nat_eq; auto.
  Qed.

  Local Hint Immediate bootstrap_Sp_nonzero bootstrap_Sp_freeable noWrap.

  Lemma break : NToW ((heapSize + 50) * 4)%N = ((heapSize' + 50) * 4)%nat.
    intros.
    unfold NToW; rewrite NToWord_nat by auto.
    unfold heapSize'; rewrite N2Nat.inj_mul; auto.
    rewrite Hide.to_nat_eq; rewrite N2Nat.inj_add; auto.
  Qed.

  Lemma times4 : (Hide.heapSize4 heapSize : W) = (heapSize' * 4)%nat.
    rewrite Hide.heapSize4_eq; intros.
    unfold NToW; rewrite NToWord_nat by auto.
    unfold heapSize'; rewrite N2Nat.inj_mul; auto.
    rewrite Hide.to_nat_eq; auto.
  Qed.

  Lemma wordToNat_heapSize : wordToNat (NToW heapSize) = heapSize'.
    unfold heapSize'; rewrite Hide.to_nat_eq.
    unfold NToW.
    rewrite NToWord_nat.
    apply wordToNat_natToWord_idempotent.
    eapply goodSize_weaken.
    2: instantiate (1 := (heapSize' * 4)%nat).
    auto.
    unfold heapSize'; rewrite Hide.to_nat_eq; auto.
  Qed.

  Hint Rewrite break times4 wordToNat_heapSize : sepFormula.

  Ltac t := genesis; rewrite natToW_plus; reflexivity.

  Theorem okb : moduleOk boot.
    unfold boot; rewrite <- Hide.heapSize4_eq; vcgen; abstract t.
  Qed.

  Global Opaque heapSize'.

  Definition m1 := link boot m0.
  Definition m2 := link Buffers.m m1.
  Definition m3 := link XmlLex.m m2.
  Definition m4 := link Malloc.m m3.
  Definition m := link (XmlLang.m pr) m4.

  Lemma ok1 : moduleOk m1.
    link okb ok0.
  Qed.

  Lemma ok2 : moduleOk m2.
    link Buffers.ok ok1.
  Qed.

  Lemma ok3 : moduleOk m3.
    link XmlLex.ok ok2.
  Qed.

  Lemma ok4 : moduleOk m4.
    link Malloc.ok ok3.
  Qed.

  Lemma ok : moduleOk m.
    link (XmlLang.ok pr wellFormed inScope) ok4.
  Qed.
  
  Variable stn : settings.
  Variable prog : IL.program.
  
  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl,
    LabelMap.MapsTo l (pre, bl) (XCAP.Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (XCAP.Imports m)
    -> exists w, Labels stn l = Some w
      /\ prog w = None.

  Hypothesis omitImp : forall l w,
    Labels stn ("sys", l) = Some w
    -> prog w = None.

  Variable w : W.
  Hypothesis at_start : Labels stn ("main", Global "main") = Some w.

  Variable st : state.

  Hypothesis prec : forall specs, interp specs (Precondition bootS None (stn, st)).

  Import Safety.

  Theorem safe : sys_safe stn prog (w, st).
    eapply safety; try eassumption; [
      link_simp; unfold labelSys, labelSys'; simpl; tauto
      | apply ok
      | apply LabelMap.find_2; link_simp; reflexivity
      | auto ].
  Qed.
End boot.

End Make.
