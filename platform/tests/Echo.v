Require Import AutoSep Malloc Arrays8.


Definition mainS := SPEC reserving 12
  PREonly[_] mallocHeap 0.

Opaque allocated.

Definition m := bimport [[ "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS],
                           "sys"!"listen" @ [listenS], "sys"!"accept" @ [acceptS],
                           "sys"!"read" @ [readS], "sys"!"write" @ [writeS],
                           "malloc"!"malloc" @ [mallocS] ]]
  bmodule "test" {{
    bfunctionNoRet "main"("fdl", "fd", "buf", "n") [mainS]
      "fdl" <-- Call "sys"!"listen"(8080%N)
      [PREonly[_] mallocHeap 0];;

      "fd" <-- Call "sys"!"accept"("fdl")
      [PREonly[_] mallocHeap 0];;

      "buf" <-- Call "malloc"!"malloc"(0, 10)
      [PREonly[_, R] R =?> 10];;

      Note [please_materialize_buffer 10];;

      "n" <-- Call "sys"!"read"("fd", "buf", 40)
      [PREonly[V] V "buf" =?>8 40];;

      [PREonly[V] V "buf" =?>8 40]
      While ("n" <> 0) {
        Call "sys"!"printInt"("n")
        [PREonly[V] V "buf" =?>8 40];;

        "n" <-- Call "sys"!"read"("fd", "buf", 40)
        [PREonly[V] V "buf" =?>8 40]
      };;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Definition hints : TacPackage.
  prepare materialize_buffer tt.
Defined.

Ltac t := solve [ sep hints; auto ].

Theorem ok : moduleOk m.
  vcgen; abstract (sep hints; auto).
Qed.
