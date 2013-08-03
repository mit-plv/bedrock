Require Import Bedrock XmlTestDriver AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
