Require Import Bedrock WebServerDriver AMD64_gas.

Module M.
  Definition heapSize := (1024 * 1024 * 25)%N.
End M.

Module E := Make(M).

Set Printing Depth 999999.
Eval compute in moduleS E.m.
