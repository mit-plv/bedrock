Require Import Thread0 BabyThread Bootstrap.


Module Type S.
  Variable heapSize : nat.
End S.

Module Make(M : S).
Import M.

Module M'.
  Definition globalSched : W := (heapSize + 50) * 4.
End M'.

Import M'.

Module E := BabyThread.Make(M').
Import E.

Section boot.
  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.

  Definition size := heapSize + 50 + 1.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize * 4).
    goodSize.
  Qed.

  Definition bootS := bootS heapSize 1.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "test"!"main" @ [E.mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%nat;;

        Assert [PREonly[_] globalSched =?> 1 * 0 =?> heapSize];;

        Call "malloc"!"init"(0, heapSize)
        [PREonly[_] globalSched =?> 1 * mallocHeap 0];;

        Call "test"!"main"()
        [PREonly[_] [| False |] ]
      end
    }}.

  Theorem ok : moduleOk boot.
    vcgen; abstract (unfold globalSched; genesis).
  Qed.

  Definition m0 := link Malloc.m boot.
  Definition m1 := link Queue.m m0.
  Definition m2 := link E.T.T.Q''.m m1.
  Definition m3 := link E.T.T.Q''.Q'.m m2.
  Definition m4 := link E.T.T.Q''.Q'.Q.m m3.
  Definition m5 := link E.m m4.

  Lemma ok0 : moduleOk m0.
    link Malloc.ok ok.
  Qed.

  Lemma ok1 : moduleOk m1.
    link Queue.ok ok0.
  Qed.

  Lemma ok2 : moduleOk m2.
    link E.T.T.Q''.ok ok1.
  Qed.

  Lemma ok3 : moduleOk m3.
    link E.T.T.Q''.Q'.ok ok2.
  Qed.

  Lemma ok4 : moduleOk m4.
    link E.T.T.Q''.Q'.Q.ok ok3.
  Qed.

  Lemma ok5 : moduleOk m5.
    link E.ok ok4.
  Qed.

  Variable stn : settings.
  Variable prog : program.
  
  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl,
    LabelMap.MapsTo l (pre, bl) (XCAP.Blocks m5)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Variable w : W.
  Hypothesis at_start : Labels stn ("main", Global "main") = Some w.

  Variable st : state.

  Hypothesis mem_low : forall n, (n < size * 4)%nat -> st.(Mem) n <> None.
  Hypothesis mem_high : forall w, $(size * 4) <= w -> st.(Mem) w = None.

  Theorem safe : safe stn prog (w, st).
    safety ok5.
  Qed.
End boot.

End Make.
