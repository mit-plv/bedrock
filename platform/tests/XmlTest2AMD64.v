Require Import Bedrock XmlTest2Driver AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
