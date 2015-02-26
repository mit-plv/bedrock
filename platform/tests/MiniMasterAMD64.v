Require Import Bedrock.Bedrock Platform.tests.MiniMasterDriver Bedrock.AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
