Require Import Bedrock Xml XmlProg.

Module M.
  Definition ts := {| Name := "params";
    Address := ((1024 * 1024 + 50) * 4)%N;
    Schema := "key" :: "value" :: nil
  |} :: nil.

  Definition pr := (
    Match
      "methodCall"/(
        "methodName"/"get"
        & "params"/(
          "param"/(
            "value"/(
              "string"/$"key"
            )
          )
        )
      )
    Do
      From "params" Where ("key" = $"key")
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
                        "Value is"
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
    end;;
    Match
      "methodCall"/(
        "methodName"/"set"
        & "params"/(
          "param"/(
            "value"/(
              "string"/$"key"
            )
          );;
          "param"/(
            "value"/(
              "string"/$"value"
            )
          )
        )
      )
    Do
      Insert "params" ($"key", $"value");;
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
                      "OK"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>
                </>
              </>
            </>
          </>
        </>
      </>
    end;;
    Match
      "methodCall"/(
        "methodName"/"delete"
        & "params"/(
          "param"/(
            "value"/(
              "string"/$"key"
            )
          )
        )
      )
    Do
      Delete "params" Where ("key" = $"key");;
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
                      "OK"
                    </>
                  </>,
                  <*> "value" </>
                    <*> "int" </>
                      "1"
                    </>
                  </>
                </>
              </>
            </>
          </>
        </>
      </>
    end
  )%program.

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
