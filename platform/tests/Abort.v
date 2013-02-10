Require Import AutoSep Sys.


Definition mainS := SPEC reserving 0
  PREonly[_] Emp.

Definition m := bimport [[ "sys"!"abort" @ [abortS] ]]
  bmodule "test" {{
    bfunctionNoRet "main"() [mainS]
      Goto "sys"!"abort"
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
