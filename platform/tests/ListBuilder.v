Require Import Thread SinglyLinkedList.


Definition handlerS := SPEC("sc") reserving 24
  PREonly[V] sched (V "sc") * mallocHeap 0.

Definition mainS := SPEC reserving 23
  PREonly[_] mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS], "scheduler"!"yield" @ [yieldS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("sc", "i", "p", "r") [handlerS]
      "i" <- 0;; (* Loop counter *)
      "p" <- 0;; (* Pointer to head of list we will build *)

      [PREonly[V] Ex ls, sll ls (V "p") * sched (V "sc") * mallocHeap 0]
      While ("i" < 10) {
        "r" <-- Call "malloc"!"malloc"(0, 2)
        [PREonly[V, R] [| R <> 0 |] * [| freeable R 2 |] * R =?> 2 * Ex ls, sll ls (V "p") * sched (V "sc") * mallocHeap 0];;

        "r" *<- "i";;
        "r" + 4 *<- "p";;
        "p" <- "r";;
        "i" <- "i" + 1;;

        Yield
        [PREonly[V] Ex ls, sll ls (V "p") * sched (V "sc") * mallocHeap 0]
      };;

      [PREonly[V] Ex ls, sll ls (V "p") * sched (V "sc") * mallocHeap 0]
      While ("p" <> 0) {
        "r" <- "p";;
        "p" <-* "p" + 4;;
        Call "malloc"!"free"(0, "r", 2)
        [PREonly[V, R] Ex ls, sll ls (V "p") * sched (V "sc") * mallocHeap 0];;

        Yield
        [PREonly[V] Ex ls, sll ls (V "p") * sched (V "sc") * mallocHeap 0]
      };;

      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      "sc" <-- Call "scheduler"!"init"()
      [PREonly[_, R] sched R * mallocHeap 0];;

      Spawn("test"!"handler", 26)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      Spawn("test"!"handler", 26)
      [PREonly[V] sched (V "sc") * mallocHeap 0];;

      Go
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep hints.
Qed.
