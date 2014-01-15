Set Implicit Arguments.

Require Import Labels.
Require Import Label.

Definition to_bedrock_label (l : label) : Labels.label := (fst l, Global (snd l)).

Coercion to_bedrock_label : label >-> Labels.label.

Definition from_bedrock_label_map A (f : Labels.label -> A) (lbl : Label.label) := f lbl.

