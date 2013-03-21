Require Import Bedrock EchoServerDriver AMD64_gas.

Module M.
  Definition heapSize := 1024.
  Definition port : W := 8081%N.
  Definition numWorkers : W := 2.
End M.

Module E := Make(M).

Set Printing Depth 999999.
Eval compute in moduleS E.m.
