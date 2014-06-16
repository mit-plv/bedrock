Require Import Thread0 Bootstrap.


Module Type S.
  Parameter heapSize : nat.
End S.

Module Make(M : S).
Import M.

Module M'.
  Definition globalSched : W := ((heapSize + 50) * 4)%nat.
End M'.
Import M'.

Module T := Thread0.Make(M').

Section boot.
  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.

  Definition size := heapSize + 50 + 1.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize * 4).
    goodSize.
  Qed.

  Definition appmainS := SPEC reserving 49
    PREonly[_] mallocHeap 0.

  Definition bootS := bootS heapSize 1.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "app"!"main" @ [appmainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%nat;;

        Assert [PREmain[_] globalSched =?> 1 * 0 =?> heapSize];;

        Call "malloc"!"init"(0, heapSize)
        [PREmain[_] globalSched =?> 1 * mallocHeap 0];;

        Goto "app"!"main"
      end
    }}.

  Ltac t := unfold globalSched, localsInvariantMain, globalSched; genesis.

  Theorem ok0 : moduleOk boot.
    vcgen; abstract t.
  Qed.

  Definition m := link boot T.T.m.

  Theorem ok : moduleOk m.
    link ok0 T.T.ok.
  Qed.

  (* No final proof here, because that crucial app.main() function is outside the
   * scope of Bedrock! *)
End boot.

End Make.
