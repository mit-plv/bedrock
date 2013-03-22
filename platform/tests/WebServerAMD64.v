Require Import Bedrock WebServerDriver AMD64_gas.

Module M.
  Definition heapSize := (1024 * 1024 * 25)%N.
  Definition port : W := 8080%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).

Set Printing Depth 999999.
Eval compute in moduleS E.m.
