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


  Definition m0 := link Malloc.m boot.
  Definition m1 := link Queue.m m0.
  Definition m2 := link Scheduler.m m1.
  Definition m3 := link BabyThread.m m2.
End boot.
