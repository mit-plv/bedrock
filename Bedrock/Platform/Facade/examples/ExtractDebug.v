Definition level0 := 1.

Extraction "extractDebug.ml" level0.

Module Type ADT.

  Parameter ADTValue : Type.

End ADT.

Module Type RepInv (E : ADT).
  
  Parameter rep_inv : E.ADTValue.

End RepInv.

Module NatADT <: ADT.

    Definition ADTValue := nat.

End NatADT.

Module NatRepInv <: RepInv NatADT.
  
    Definition rep_inv := 1.

End NatRepInv.

Module File1.

  Module Make (E : ADT) (M : RepInv E).
    
    Definition value := M.rep_inv.
               
  End Make.

End File1.

Module Level1 := File1.Make NatADT NatRepInv.
Definition level1 := Level1.value.

Extraction "extractDebug.ml" level1.

Module File2.

  Module Make (E : ADT) (M : RepInv E).
    
    Module Made := File1.Make E M.
    Definition value := Made.value.
               
  End Make.

End File2.

Module Level2 := File2.Make NatADT NatRepInv.
Definition level2 := Level2.value.

Extraction "extractDebug.ml" level2.

Module File3.

  Module Make (E : ADT) (M : RepInv E).
    
    Module Made := File2.Make E M.
    Definition value := Made.value.
               
  End Make.

End File3.

Module Level3 := File3.Make NatADT NatRepInv.
Definition level3 := Level3.value.

Extraction "extractDebug.ml" level3.
