Set Implicit Arguments.

Require Import Facade.
Require Import Notations.

Section ADTValue.

  Variable ADTValue : Type.
  Variables ArraySeq_newSpec ArraySeq_writeSpec ArraySeq_readSpec ArraySeq_deleteSpec ListSet_newSpec ListSet_addSpec ListSet_sizeSpec ListSet_deleteSpec : AxiomaticSpec ADTValue.

  Local Open Scope facade_scope.
  Local Open Scope list_scope.

  Definition m := 
    fmodule "count" 
    import [[
          "ADT"!"ArraySeq_new" @ [ArraySeq_newSpec],
          "ADT"!"ArraySeq_write" @ [ArraySeq_writeSpec],
          "ADT"!"ArraySeq_read" @ [ArraySeq_readSpec],
          "ADT"!"ArraySeq_delete" @ [ArraySeq_deleteSpec],
          "ADT"!"ListSet_new" @ [ListSet_newSpec],
          "ADT"!"ListSet_add" @ [ListSet_addSpec],
          "ADT"!"ListSet_size" @ [ListSet_sizeSpec],
          "ADT"!"ListSet_delete" @ [ListSet_deleteSpec]
    ]]
    define {{
      ffunction "count"("arr", "len")
        "set" <-- DCall "ADT"!"ListSet_new"();;
        "i" <- 0;;
        While ("i" < "len") {
          "e" <-- DCall "ADT"!"ArraySeq_read" ("arr", "i");;
          DCall "ADT"!"ListSet_add"("set", "e");;
          "i" <- "i" + 1
        };;
        "ret" <-- DCall "ADT"!"ListSet_size"("set");;
        DCall "ADT"!"ListSet_delete"("set")
      end with
      ffunction "main"()
(*
        "arr" <-- DCall "ADT"!"ArraySeq_new"(3);;
        DCall "ADT"!"ArraySeq_write"("arr", 0, 10);;
        DCall "ADT"!"ArraySeq_write"("arr", 1, 20);;
        DCall "ADT"!"ArraySeq_write"("arr", 2, 10);;
        "ret" <-- DCall "count"!"count" ("arr", 3);;
        DCall "ADT"!"ArraySeq_delete"("arr")
*)
        "ret" <- 0
      end
    }}.

  Require Import Facade.CompileModule.

  Definition cmodule := compile (fst m) eq_refl (snd m).

End ADTValue.