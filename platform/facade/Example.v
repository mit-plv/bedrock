Set Implicit Arguments.

Require Import Facade.
Require Import Notations.

Section ADTValue.

  Variable ADTValue : Type.
  Variables ArraySeq_newSpec ArraySeq_writeSpec ArraySeq_readSpec ArraySeq_deleteSpec ListSet_newSpec ListSet_addSpec ListSet_sizeSpec ListSet_deleteSpec : AxiomaticSpec ADTValue.

  Local Open Scope facade_scope.
  Local Open Scope list_scope.

  Definition m := 
    module
    import {
      "ADT"!"ArraySeq_new" ==> ArraySeq_newSpec;
      "ADT"!"ArraySeq_write" ==> ArraySeq_writeSpec;
      "ADT"!"ArraySeq_read" ==> ArraySeq_readSpec;
      "ADT"!"ArraySeq_delete" ==> ArraySeq_deleteSpec;
      "ADT"!"ListSet_new" ==> ListSet_newSpec;
      "ADT"!"ListSet_add" ==> ListSet_addSpec;
      "ADT"!"ListSet_size" ==> ListSet_sizeSpec;
      "ADT"!"ListSet_delete" ==> ListSet_deleteSpec
    }
    define {
      def "count" = func("arr", "len")
        "set" <-- call_ "ADT"!"ListSet_new"();;
        "i" <- 0;;
        while_ ("i" < "len") {
          "e" <-- call_ "ADT"!"ArraySeq_read" ("arr", "i");;
          call_ "ADT"!"ListSet_add"("set", "e");;
          "i" <- "i" + 1
        };;
        "ret" <-- call_ "ADT"!"ListSet_size"("set");;
        call_ "ADT"!"ListSet_delete"("set")
      end;
      def "main" = func()
(*
        "arr" <-- call_ "ADT"!"ArraySeq_new"(3);;
        call_ "ADT"!"ArraySeq_write"("arr", 0, 10);;
        call_ "ADT"!"ArraySeq_write"("arr", 1, 20);;
        call_ "ADT"!"ArraySeq_write"("arr", 2, 10);;
        "ret" <-- call_ "count"!"count" ("arr", 3);;
        call_ "ADT"!"ArraySeq_delete"("arr")
*)
        "ret" <- 0
      end
    }.

  Require Import Facade.CompileModule.

  Definition cmodule := compile (fst m) eq_refl (snd m).

End ADTValue.