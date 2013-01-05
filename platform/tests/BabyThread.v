Require Import Thread.


Definition handlerS := SPEC("sc") reserving 14
  PREonly[V] sched (V "sc") * mallocHeap 0.

Definition mainS := SPEC reserving 23
  PREonly[_] mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("sc") [handlerS]
      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      "sc" <-- Call "scheduler"!"init"()
      [PREonly[_, R] sched R * mallocHeap 0];;

      Spawn("test"!"handler", 16)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      (*Spawn("sc", "test"!"handler", 16)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;*)

      Go
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
