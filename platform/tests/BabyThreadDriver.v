Require Import Thread BabyThread Bootstrap.


Notation "'bfunctionNoRet' name () [ p ] b 'end'" :=
  (let p' := p in
   let vars := nil in
   let b' := b%SP in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := ((fun _ _ =>
        Structured nil (fun im mn _ => Structured.Assert_ im mn (Precondition p' (Some vars))));;
      (fun ns res => b' ns (res - (List.length vars - List.length (Formals p')))%nat))%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Section boot.
  Variable heapSize : nat.

  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.
  Hypothesis heapSizeUpperBound : goodSize (4 * heapSize).

  Lemma goodSize_heapSize : goodSize heapSize.
    eapply goodSize_weaken; [ eassumption | omega ].
  Qed.

  Hint Immediate goodSize_heapSize.

  Theorem heapSizeLowerBound' : natToW 3 <= natToW heapSize.
    intro; pre_nomega.
    rewrite wordToNat_natToWord_idempotent in *.
    rewrite wordToNat_natToWord_idempotent in *.
    omega.
    reflexivity.
    change (goodSize heapSize); eapply goodSize_weaken; [ eassumption | omega ].
  Qed.

  Hint Immediate heapSizeLowerBound'.

  Theorem noWrap : noWrapAround (natToW (0 + 4)) (wordToNat (natToW heapSize) - 1).
    simpl; hnf; intros.
    intro.
    rewrite <- natToW_plus in H0.
    apply natToW_inj in H0.
    omega.
    2: reflexivity.
    rewrite wordToNat_natToWord_idempotent in *.
    eapply goodSize_weaken; [ eassumption | omega ].
    change (goodSize heapSize); eauto.
  Qed.

  Hint Extern 1 (noWrapAround _ _) => apply noWrap.

  Theorem heapSize_roundTrip : wordToNat (natToW heapSize) = heapSize.
    intros; apply wordToNat_natToWord_idempotent;
      change (goodSize heapSize); eauto.
  Qed.

  Hint Rewrite heapSize_roundTrip : sepFormula.

  Definition bootS := SPEC reserving 50
    PREonly[_] 0 =?> heapSize.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "test"!"main" @ [BabyThread.mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Call "malloc"!"init"(0, heapSize)
        [PREonly[_] mallocHeap 0];;

        Call "test"!"main"()
        [PREonly[_] [| False |] ];;

        Fail
      end
    }}.

  Theorem ok : moduleOk boot.
    vcgen; abstract sep_auto.
  Qed.

  Ltac link_simp := simpl Imports; simpl Exports;
    cbv beta iota zeta delta [importsOk LabelMap.fold LabelMap.Raw.fold
      LabelMap.this importsMap fold_left LabelMap.add LabelMap.Raw.add
      LabelMap.empty LabelMap.Raw.empty
      LabelKey.compare LabelKey.compare' string_lt
      fst snd string_dec sumbool_rec sumbool_rect
      Ascii.N_of_ascii Ascii.N_of_digits N.compare Pos.compare
      string_rec string_rect Ascii.ascii_dec
      LabelMap.find LabelMap.Raw.find Nplus Nmult Pos.compare_cont
      Pos.add Pos.mul Ascii.ascii_rec Ascii.ascii_rect
      Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym
      label'_lt label'_eq label'_rec label'_rect
      LabelMap.Raw.bal LabelMap.Raw.create
      Int.Z_as_Int.gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.ge_lt_dec
      LabelMap.Raw.height
      ZArith_dec.Z_gt_le_dec Int.Z_as_Int._0
      BinInt.Z.add Int.Z_as_Int._1 Int.Z_as_Int._2
      ZArith_dec.Z_gt_dec ZArith_dec.Z_ge_lt_dec Int.Z_as_Int.max
      BinInt.Z.max BinInt.Z.compare union ZArith_dec.Z_ge_dec
      diff LabelMap.mem LabelMap.Raw.mem LabelMap.is_empty
      LabelMap.Raw.is_empty Pos.succ].

  Ltac link m1 m2 :=
    apply linkOk; [ apply m1 | apply m2 | exact (refl_equal true)
      | link_simp; tauto | link_simp; tauto | link_simp; tauto ].

  Definition m0 := link Malloc.m boot.
  Definition m1 := link Queue.m m0.
  Definition m2 := link Scheduler.m m1.
  Definition m3 := link BabyThread.m m2.

  Lemma ok0 : moduleOk m0.
    link Malloc.ok ok.
  Qed.

  Lemma ok1 : moduleOk m1.
    link Queue.ok ok0.
  Qed.

  Lemma ok2 : moduleOk m2.
    link Scheduler.ok ok1.
  Qed.

  Lemma ok3 : moduleOk m3.
    link BabyThread.ok ok2.
  Qed.
End boot.
