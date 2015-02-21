Require Import Bedrock MiniMasterDriver I386_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
