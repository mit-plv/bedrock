Require Import Thread SinglyLinkedList.


Module Type S.
  Variables globalList globalSched : W.
End S.

Module Make(M : S).
Import M.

Module M'''.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv : HProp := Ex p, globalList =*> p * Ex ls, sll ls p.
End M'''.

Ltac unf := unfold M'''.globalSched, M'''.globalInv in *.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Ltac sep := T.sep unf SinglyLinkedList.hints.

Definition handlerS := SPEC reserving 29
  PREonly[_] sched * globalInv * mallocHeap 0.

Definition mainS := SPEC reserving 36
  PREonly[_] globalSched =?> 1 * globalList =?> 1 * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS], "scheduler"!"yield" @ [yieldS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("i", "p", "r") [handlerS]
      "i" <- 0;; (* Loop counter *)

      [PREonly[_] sched * globalInv * mallocHeap 0]
      While ("i" < 10) {
        "r" <-- Call "malloc"!"malloc"(0, 2)
        [PREonly[V, R] [| R <> 0 |] * [| freeable R 2 |] * R =?> 2 * sched * globalInv * mallocHeap 0];;

        "r" *<- "i";;
        "p" <-* globalList;;
        "r" + 4 *<- "p";;
        globalList *<- "r";;
        "i" <- "i" + 1;;

        Yield
        [PREonly[_] sched * globalInv * mallocHeap 0]
      };;

      "p" <-* globalList;;
      [PREonly[V] sched * globalList =*> V "p" * Ex ls, sll ls (V "p") * mallocHeap 0]
      While ("p" <> 0) {
        "r" <- "p";;
        "p" <-* "p" + 4;;
        globalList *<- "p";;
        Call "malloc"!"free"(0, "r", 2)
        [PREonly[_] sched * globalInv * mallocHeap 0];;

        Yield
        [PREonly[_] sched * globalInv * mallocHeap 0];;

        "p" <-* globalList
      };;

      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      globalList *<- 0;;

      Init
      [PREonly[_] sched * globalInv * mallocHeap 0];;

      Spawn("test"!"handler", 30)
      [PREonly[_] sched * globalInv * mallocHeap 0];;

      Spawn("test"!"handler", 30)
      [PREonly[_] sched * globalInv * mallocHeap 0];;

      Go
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep.
Qed.

End Make.
