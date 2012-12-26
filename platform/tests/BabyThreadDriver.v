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
  Variables heapSize : nat.

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

  Definition bootS := {|
    Reserved := 49;
    Formals := nil;
    Precondition := fun _ => st ~> ![ 0 =?> (heapSize + 50) ] st
  |}.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "test"!"main" @ [BabyThread.mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%nat;;

        Assert [PREonly[_] 0 =?> heapSize];;

        Call "malloc"!"init"(0, heapSize)
        [PREonly[_] mallocHeap 0];;

        Call "test"!"main"()
        [PREonly[_] [| False |] ];;

        Fail
      end
    }}.

  Lemma create_stack : forall ns ss sp,
    NoDup ns
    -> sp =?> (length ns + ss) ===> Ex vs, locals ns vs ss sp.
    intros; eapply Himp_trans; [ apply allocated_split | ].
    instantiate (1 := length ns); omega.
    eapply Himp_trans.
    eapply Himp_star_frame.
    apply behold_the_array; auto.
    apply Himp_refl.
    unfold locals, array.
    Opaque mult.
    sepLemma.
    apply allocated_shift_base.
    Require Import Arith.
    unfold natToW; rewrite mult_comm; words.
    omega.
  Qed.

  Theorem genesis :
    0 =?> (heapSize + 50)
    ===> (Ex vs, locals ("rp" :: nil) vs 49 (heapSize * 4)%nat) * 0 =?> heapSize.
    descend; intros; eapply Himp_trans; [ apply allocated_split | ].
    instantiate (1 := heapSize); auto.
    apply Himp_trans with (0 =?> heapSize *
      (heapSize * 4)%nat =?> 50)%Sep.
    apply Himp_star_frame.
    apply Himp_refl.
    apply allocated_shift_base.
    Require Import Arith.
    rewrite mult_comm.
    simpl.
    unfold natToW.
    words.
    omega.
    apply Himp_trans with (0 =?> heapSize *
      Ex vs, locals ("rp" :: nil) vs 49 (heapSize * 4)%nat)%Sep.
    apply Himp_star_frame.
    apply Himp_refl.
    change 50 with (length ("rp" :: nil) + 49).
    apply create_stack.
    NoDup.
    sepLemma.
  Qed.

  Transparent mult.

  Definition genesisHints : TacPackage.
    prepare genesis tt.
  Defined.

  Theorem ok : moduleOk boot.
    vcgen; abstract sep genesisHints.
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

  Variable stn : settings.
  Variable prog : program.
  
  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl,
    LabelMap.MapsTo l (pre, bl) (XCAP.Blocks m3)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Variable w : W.
  Hypothesis at_start : Labels stn ("main", Global "main") = Some w.

  Variable st : state.

  Definition size := heapSize + 50.

  Hypothesis mem_low : forall n, (n < 4 * size)%nat -> st.(Mem) n <> None.
  Hypothesis mem_high : forall w, $(4 * size) <= w -> st.(Mem) w = None.
  Hypothesis mem_size : goodSize (4 * size)%nat.

  Ltac safety ok :=
    eapply XCAP.safety; try apply ok; try eassumption; [
      reflexivity
      | apply LabelMap.find_2; link_simp; reflexivity
      | propxFo; descend; apply materialize_allocated; assumption ].

  Theorem safe : safe stn prog (w, st).
    safety ok3.
  Qed.
End boot.
