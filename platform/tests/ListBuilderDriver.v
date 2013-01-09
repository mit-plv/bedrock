Require Import Thread0 ListBuilder Bootstrap.


Section boot.
  Variable heapSize : nat.

  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.

  Definition size := heapSize + 50.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize * 4).
    goodSize.
  Qed.

  Definition bootS := bootS heapSize.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "test"!"main" @ [ListBuilder.mainS] ]]
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

  Theorem ok : moduleOk boot.
    vcgen; abstract (sep genesisHints; eauto).
  Qed.

  Definition m0 := link Malloc.m boot.
  Definition m1 := link Queue.m m0.
  Definition m2 := link Q.m m1.
  Definition m3 := link ListBuilder.m m2.

  Lemma ok0 : moduleOk m0.
    link Malloc.ok ok.
  Qed.

  Lemma ok1 : moduleOk m1.
    link Queue.ok ok0.
  Qed.

  Lemma ok2 : moduleOk m2.
    link Q.ok ok1.
  Qed.

  Lemma ok3 : moduleOk m3.
    link ListBuilder.ok ok2.
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

  Hypothesis mem_low : forall n, (n < size * 4)%nat -> st.(Mem) n <> None.
  Hypothesis mem_high : forall w, $(size * 4) <= w -> st.(Mem) w = None.

  Theorem safe : safe stn prog (w, st).
    safety ok3.
  Qed.
End boot.
