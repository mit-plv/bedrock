Require Import Bedrock Factorial AMD64_gas.

Definition compiled := moduleS factProg.
Recursive Extraction compiled.
