Require Import Thread SinglyLinkedList.


Parameter globalList : W.

Module M.
  Open Scope Sep_scope.

  Definition realInv : HProp := Ex p, globalList =*> p * Ex ls, sll ls p.

  Definition globalInv (_ : W) : hpropB ((settings * state : Type)%type :: nil) :=
    ^[realInv].
End M.

Module T := Make(M).
Import M T.

Ltac sep := T.sep ltac:(unfold globalInv, realInv in *) SinglyLinkedList.hints.


Definition handlerS := SPEC("sc") reserving 24
  PREonly[V] tq (V "sc") * realInv * mallocHeap 0.

Definition mainS := SPEC reserving 23
  PREonly[_] globalList =?> 1 * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "threadq"!"init" @ [initS], "threadq"!"exit" @ [exitS],
                           "threadq"!"spawn" @ [spawnS], "threadq"!"yield" @ [yieldS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("sc", "i", "p", "r") [handlerS]
      "i" <- 0;; (* Loop counter *)

      [PREonly[V] tq (V "sc") * realInv * mallocHeap 0]
      While ("i" < 10) {
        "r" <-- Call "malloc"!"malloc"(0, 2)
        [PREonly[V, R] [| R <> 0 |] * [| freeable R 2 |] * R =?> 2 * tq (V "sc") * realInv * mallocHeap 0];;

        "r" *<- "i";;
        "p" <-* globalList;;
        "r" + 4 *<- "p";;
        globalList *<- "r";;
        "i" <- "i" + 1;;

        Yield
        [PREonly[V] tq (V "sc") * realInv * mallocHeap 0]
      };;

      "p" <-* globalList;;
      [PREonly[V] tq (V "sc") * globalList =*> V "p" * Ex ls, sll ls (V "p") * mallocHeap 0]
      While ("p" <> 0) {
        "r" <- "p";;
        "p" <-* "p" + 4;;
        globalList *<- "p";;
        Call "malloc"!"free"(0, "r", 2)
        [PREonly[V] tq (V "sc") * realInv * mallocHeap 0];;

        Yield
        [PREonly[V] tq (V "sc") * realInv * mallocHeap 0];;

        "p" <-* globalList
      };;

      Exit
    end with bfunctionNoRet "main"("sc") [mainS]
      globalList *<- 0;;

      "sc" <-- Call "threadq"!"init"()
      [PREonly[_, R] tq R * realInv * mallocHeap 0];;

      Spawn("test"!"handler", 26)
      [PREonly[V] tq (V "sc") * realInv * mallocHeap 0];;

      Spawn("test"!"handler", 26)
      [PREonly[V] tq (V "sc") * realInv * mallocHeap 0];;

      Go
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep.
Qed.
