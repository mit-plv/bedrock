Require Import Thread.


Definition handlerS := SPECthd reserving 14
  PREonly[_] Emp.

Definition mainS := SPEC reserving 23
  PREonly[_] mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    tfunctionNoRet "handler"() [handlerS]
      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      "sc" <-- Call "scheduler"!"init"()
      [PREonly[_, R] sched R * mallocHeap 0];;

      Spawn("sc", "test"!"handler", 16)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      Spawn("sc", "test"!"handler", 16)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      Go "sc"
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
