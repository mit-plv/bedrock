Require Import Thread0.


Module Make(M : S).
Import M.

Module T := Thread0.Make(M).
Import T.

Definition handlerS := SPEC reserving 19
  PREonly[_] sched * mallocHeap 0.

Definition mainS := SPEC reserving 36
  PREonly[_] globalSched =?> 1 * mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"() [handlerS]
      Exit
    end with bfunctionNoRet "main"() [mainS]
      Init
      [PREonly[_] sched * mallocHeap 0];;

      Spawn("test"!"handler", 20)
      [PREonly[_] sched * mallocHeap 0];;

      Spawn("test"!"handler", 20)
      [PREonly[_] sched * mallocHeap 0];;

      Go
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.

End Make.
