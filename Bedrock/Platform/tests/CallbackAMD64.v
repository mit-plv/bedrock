Require Import Bedrock.Bedrock Bedrock.Platform.tests.CallbackDriver Bedrock.AMD64_gas.

Definition compiled := moduleS E.m.
Unset Extraction AccessOpaque.  Recursive Extraction compiled.
