Require Import Bedrock.Bedrock Bedrock.Examples.Factorial Bedrock.AMD64_gas.

Definition compiled := moduleS factProg.
Unset Extraction AccessOpaque.  Recursive Extraction compiled.
