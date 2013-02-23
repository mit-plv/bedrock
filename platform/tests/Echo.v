Require Import AutoSep.


Definition mainS := SPEC reserving 4
  PREonly[_] Emp.

Definition m := bimport [[ "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS],
                           "sys"!"listen" @ [listenS], "sys"!"accept" @ [acceptS],
                           "sys"!"read" @ [readS], "sys"!"write" @ [writeS] ]]
  bmodule "test" {{
    bfunctionNoRet "main"("fdl", "fd") [mainS]
      "fdl" <-- Call "sys"!"listen"(8080%N)
      [PREonly[_] Emp];;

      "fd" <-- Call "sys"!"accept"("fdl")
      [PREonly[_] Emp];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
