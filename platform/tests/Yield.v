Require Import Thread.


Definition handlerS := SPEC("sc") reserving 21
  PREonly[V] sched (V "sc") * mallocHeap 0.

Definition mainS := SPEC reserving 23
  PREonly[_] mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS], "scheduler"!"yield" @ [yieldS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("sc") [handlerS]
      Yield
      [PREonly[V] sched (V "sc") * mallocHeap 0];;
      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      "sc" <-- Call "scheduler"!"init"()
      [PREonly[_, R] sched R * mallocHeap 0];;

      Spawn("test"!"handler", 23)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      Go
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
