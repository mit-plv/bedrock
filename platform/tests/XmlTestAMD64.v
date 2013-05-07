Require Import Bedrock XmlProg AMD64_gas XmlLang.

Module M.
  Definition pr := {|
    Pattern := Tag "test" (Both (Tag "toast" (Cdata "toast")) (Tag "twist" (Cdata "twist")));
    Output := "toast"
  |}.

  Theorem wellFormed : wf (Pattern pr).
    simpl; intuition.
  Qed.

  Theorem inScope : freeVar (Pattern pr) (Output pr).
    simpl; tauto.
  Qed.

  Theorem notTooGreedy : (reserved pr <= 44)%nat.
    compute; omega.
  Qed.

  Definition inbuf_size := 1024%N.

  Theorem inbuf_size_lower : (inbuf_size >= 2)%N.
    discriminate.
  Qed.
    
  Theorem inbuf_size_upper : (inbuf_size * 4 < Npow2 32)%N.
    reflexivity.
  Qed.

  Definition heapSize := (1024 * 1024)%N.
End M.

Module E := Make(M).

Set Printing Depth 999999.
Eval compute in moduleS E.m.
