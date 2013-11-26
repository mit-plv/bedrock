Require Import Bedrock MiniMasterDriver AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
