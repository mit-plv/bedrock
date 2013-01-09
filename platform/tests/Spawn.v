Require Import Thread0.


Definition handlerS := SPEC("sc") reserving 24
  PREonly[V] sched (V "sc") * mallocHeap 0.

Definition mainS := SPEC reserving 23
  PREonly[_] mallocHeap 0.

Definition m := bimport [[ "threadq"!"init" @ [initS], "threadq"!"exit" @ [exitS],
                           "threadq"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("sc") [handlerS]
      Spawn("test"!"handler", 26)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;
      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      "sc" <-- Call "threadq"!"init"()
      [PREonly[_, R] sched R * mallocHeap 0];;

      Spawn("test"!"handler", 26)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      Go
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
