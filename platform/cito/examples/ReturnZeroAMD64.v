Require Import ReturnZeroDriver.

Module M.
  Definition heapSize := 1024.
End M.

Module E := Make(M).

Require Import AMD64_gas.

Definition compiled := moduleS E.m1.

Recursive Extraction compiled.
