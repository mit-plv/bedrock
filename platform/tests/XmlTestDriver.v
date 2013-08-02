Require Import Bedrock Xml XmlProg.

Module M.
  Definition heapSize := (1024 * 1024)%N.

  Definition ts := {| Name := "rpcs";
    Address := ((heapSize + 50) * 4)%N;
    Schema := "cmd" :: "a" :: "b" :: nil
  |} :: nil.

  Definition pr := Match
    "rpc"/(
      "cmd"/"frob"
      & "mode"/$"mode"
      & "args"/(
        "string"/$"a";;
        "string"/$"b"
        )
    )
  Do
    Write <*> "answer" </>
      <*> "mode" </> $"mode" </>,
      <*> "a" </> $"a" </>,
      <*> "b" </> $"b" </>
    </>;;
    Insert "rpcs" ("frob", $"a", $"b");;
    Write <*> "extra" </>
      <*> "boring" </> "constant" </>,
      <*> "B" </> $"b" </>
    </>
  end%program.

  Theorem wellFormed : wf ts pr.
    wf.
  Qed.

  Theorem notTooGreedy : (reserved pr <= 38)%nat.
    compute; omega.
  Qed.

  Definition buf_size := 1024%N.

  Theorem buf_size_lower : (buf_size >= 2)%N.
    discriminate.
  Qed.
    
  Theorem buf_size_upper : (buf_size * 4 < Npow2 32)%N.
    reflexivity.
  Qed.

  Theorem ND : NoDup (Names ts).
    NoDup.
  Qed.

  Theorem goodSchema : twfs ts.
    goodSchema.
  Qed.
End M.

Module E := Make(M).