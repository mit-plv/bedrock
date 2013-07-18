Require Import AutoSep Bootstrap Malloc Buffers XmlLex XmlLang Arrays8 ArrayOps.


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
  Parameter ts : tables.
  Parameter pr : program.
  Axiom wellFormed : wf ts pr.
  Axiom notTooGreedy : (reserved pr <= 40)%nat.

  Parameter buf_size : N.
  Axiom buf_size_lower : (buf_size >= 2)%N.
  Axiom buf_size_upper : (buf_size * 4 < Npow2 32)%N.

  Parameter heapSize : N.

  Parameter ND : NoDup (Names ts).
  Parameter goodSchema : twfs ts.
End S.

Module Make(M : S).
Import M.

Definition mainS := SPEC reserving 49
  PREonly[_] db ts * mallocHeap 0.

Definition bsize := nat_of_N (buf_size * 4)%N.

Inductive unfold_here := UnfoldHere.
Local Hint Constructors unfold_here.

Definition hints : TacPackage.
  prepare buffer_split_tagged buffer_join_tagged.
Defined.

Definition m0 := bimport [[ "buffers"!"bmalloc" @ [bmallocS], "sys"!"abort" @ [abortS],
                            "sys"!"read" @ [Sys.readS], "sys"!"write" @ [Sys.writeS],
                            "xml_prog"!"main" @ [XmlLang.mainS ts pr] ]]
  bmodule "xml_driver" {{
    bfunctionNoRet "main"("inbuf", "len", "outbuf", "tmp") [mainS]
      "inbuf" <-- Call "buffers"!"bmalloc"(buf_size)
      [PREonly[_, R] db ts * R =?>8 bsize * mallocHeap 0];;

      "outbuf" <-- Call "buffers"!"bmalloc"(buf_size)
      [PREonly[V, R] db ts * V "inbuf" =?>8 bsize * R =?>8 bsize * mallocHeap 0];;

      [PREonly[V] db ts * V "inbuf" =?>8 bsize * V "outbuf" =?>8 bsize * mallocHeap 0]
      While (1 = 1) {
        "len" <-- Call "sys"!"read"(0, "inbuf", bsize)
        [PREonly[V] db ts * V "inbuf" =?>8 bsize * V "outbuf" =?>8 bsize * mallocHeap 0];;

        If ("len" > bsize) {
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ];;
          Fail
        } else {
          Assert [PREonly[V] db ts * buffer_splitAt (wordToNat (V "len")) (V "inbuf") bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0
            * [| wordToNat (V "len") <= bsize |]%nat ];;

          Assert [PREonly[V] db ts * V "inbuf" =?>8 wordToNat (V "len")
            * (V "inbuf" ^+ natToW (wordToNat (V "len"))) =?>8 (bsize - wordToNat (V "len"))
            * V "outbuf" =?>8 bsize * mallocHeap 0 * [| wordToNat (V "len") <= bsize |]%nat ];;

          Note [unfold_here];;

          "tmp" <-- Call "xml_prog"!"main"("inbuf", "len", "outbuf", bsize)
          [PREonly[V, R] db ts * V "inbuf" =?>8 wordToNat (V "len")
            * (V "inbuf" ^+ natToW (wordToNat (V "len"))) =?>8 (bsize - wordToNat (V "len"))
            * V "outbuf" =?>8 bsize
            * [| R <= natToW bsize |]%word * mallocHeap 0 * [| wordToNat (V "len") <= bsize |]%nat ];;

          Assert [PREonly[V] db ts * buffer_joinAt (wordToNat (V "len")) (V "inbuf") bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0 * [| V "tmp" <= natToW bsize |]%word ];;

          Assert [PREonly[V] db ts * V "inbuf" =?>8 bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0 * [| V "tmp" <= natToW bsize |]%word ];;

          Assert [PREonly[V] db ts * V "inbuf" =?>8 bsize
            * buffer_splitAt (wordToNat (V "tmp")) (V "outbuf") bsize * mallocHeap 0
            * [| wordToNat (V "tmp") <= bsize |]%nat ];;

          Assert [PREonly[V] db ts * V "inbuf" =?>8 bsize
            * V "outbuf" =?>8 wordToNat (V "tmp")
            * (V "outbuf" ^+ natToW (wordToNat (V "tmp"))) =?>8 (bsize - wordToNat (V "tmp"))
            * mallocHeap 0 * [| wordToNat (V "tmp") <= bsize |]%nat ];;

          Call "sys"!"write"(1, "outbuf", "tmp")
          [PREonly[V] db ts * V "inbuf" =?>8 bsize
            * V "outbuf" =?>8 wordToNat (V "tmp")
            * (V "outbuf" ^+ natToW (wordToNat (V "tmp"))) =?>8 (bsize - wordToNat (V "tmp"))
            * mallocHeap 0 * [| wordToNat (V "tmp") <= bsize |]%nat ];;

          Assert [PREonly[V] db ts * V "inbuf" =?>8 bsize
            * buffer_joinAt (wordToNat (V "tmp")) (V "outbuf") bsize
            * mallocHeap 0]
        }
      }
    end
  }}.

Lemma buf_size_lower'' : (buf_size < Npow2 32)%N.
  eapply Nlt_trans; [ | apply buf_size_upper ].
  specialize buf_size_lower; intros.
  pre_nomega.
  rewrite N2Nat.inj_mul.
  simpl.
  generalize dependent (N.to_nat buf_size); intros.
  change (Pos.to_nat 2) with 2 in *.
  change (Pos.to_nat 4) with 4.
  omega.
Qed.

Lemma buf_size_lower' : natToW 2 <= NToW buf_size.
  unfold NToW.
  rewrite NToWord_nat.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent.
  change (wordToNat (natToW 2)) with (nat_of_N 2).
  apply Nge_out.
  apply buf_size_lower.
  rewrite N2Nat.id.
  apply buf_size_lower''.
Qed.

Local Hint Immediate buf_size_lower'.

Lemma bsize_in : (wordToNat (NToW buf_size) * 4) = bsize.
  unfold NToW, bsize.
  rewrite NToWord_nat.
  rewrite N2Nat.inj_mul.
  rewrite wordToNat_natToWord_idempotent.
  auto.
  rewrite N2Nat.id.
  apply buf_size_lower''.
Qed.

Lemma bsize_roundTrip : wordToNat (natToW bsize) = bsize.
  apply wordToNat_natToWord_idempotent.
  unfold bsize.
  rewrite N2Nat.id.
  apply buf_size_upper.
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

  Definition size := heapSize' + 50 + length ts.

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
    Precondition := fun _ => st ~> ![ 0 =?> (heapSize' + 50 + 0) * db ts ] st
  |}.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "xml_driver"!"main" @ [mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%N;;

        Assert [PREonly[_] 0 =?> heapSize' * db ts];;

        Call "malloc"!"init"(0, heapSize)
        [PREonly[_] mallocHeap 0 * db ts];;

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

  Lemma buf_size_upper' : goodSize (4 * wordToNat (NToWord 32 buf_size)).
    red.
    rewrite Nat2N.inj_mul.
    rewrite NToWord_nat.
    rewrite wordToNat_natToWord_idempotent.
    rewrite N2Nat.id.
    rewrite Nmult_comm.
    apply buf_size_upper.
    rewrite N2Nat.id.
    clear; generalize buf_size_upper.
    generalize (Npow2 32).
    Hint Rewrite N2Nat.inj_mul : N.
    intros; nomega.
  Qed.

  Definition m1 := link boot m0.
  Definition m2 := link Buffers.m m1.
  Definition m3 := link XmlLex.m m2.
  Definition m4 := link Malloc.m m3.
  Definition m5 := link ArrayOps.m m4.
  Definition m := link (XmlLang.m wellFormed ND goodSchema
    buf_size_lower' buf_size_upper') m5.

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

  Lemma ok5 : moduleOk m5.
    link ArrayOps.ok ok4.
  Qed.

  Lemma ok : moduleOk m.
    link (XmlLang.ok wellFormed) ok5.
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
