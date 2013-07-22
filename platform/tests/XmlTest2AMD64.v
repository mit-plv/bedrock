Require Import Bedrock Xml XmlProg AMD64_gas.

Module M.
  Definition ts := {| Name := "params";
    Address := ((1024 * 1024 + 50) * 4)%N;
    Schema := "key" :: "value" :: nil
  |} :: nil.

  Definition pr := Match
    "methodCall"/(
      "methodName"/"getAndSet"
      & "params"/(
        "param"/(
          "value"/(
            "string"/$"getKey"
          )
        );;
        "param"/(
          "value"/(
            "string"/$"setKey"
          )
        );;
        "param"/(
          "value"/(
            "string"/$"setValue"
          )
        )
      )
    )
  Do
    Insert "params" ($"setKey", $"setValue");;
    From "params" Where ("key" = $"getKey")
      Write <*> "methodResponse" </>
        <*> "params" </>
          <*> "param" </>
            <*> "value" </>
              <*> "array" </>
                <*> "data" </>
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "string" </>
                      "Parameters"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "string" </>
                      ^"value"
                    </>
                  </>
                </>
              </>
            </>
          </>
        </>
      </>
  end.

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

  Definition heapSize := (1024 * 1024)%N.

  Theorem ND : NoDup (Names ts).
    NoDup.
  Qed.

  Theorem goodSchema : twfs ts.
    goodSchema.
  Qed.
End M.

Module E := Make(M).

Set Printing Depth 999999.
Eval compute in moduleS E.m.
