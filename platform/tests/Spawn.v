Require Import Thread0.


Module Make(M : S).
Import M.

Module T := Thread0.Make(M).
Import T.

Definition handlerS := SPEC reserving 36
  PREmain[_] sched * mallocHeap 0.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("x", "y") [handlerS]
      Spawn("test"!"handler", 37)
      [PREmain[_] sched * mallocHeap 0];;
      Exit 37
    end with bfunctionNoRet "main"("x", "y") [mainS]
      Init
      [PREmain[_] sched * mallocHeap 0];;

      Spawn("test"!"handler", 37)
      [PREmain[_] sched * mallocHeap 0];;

      Go 50
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract (sep_auto; auto).
Qed.

End Make.
