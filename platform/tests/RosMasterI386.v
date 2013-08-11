Require Import Bedrock RosMasterDriver I386_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
