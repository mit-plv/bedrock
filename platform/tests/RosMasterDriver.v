Require Import Ros XmlProg.

Module M.
  Definition buf_size := 1024%N.
  Definition heapSize := (1024 * 1024 * 25)%N.

  Definition ts := {| Name := "params";
    Address := ((heapSize + 50 + 2) * 4)%N;
    Schema := "key" :: "value" :: nil
  |} :: nil.

  Definition pr := (
    RosCommand "setParam"(!string $"caller_id", !string $"key", !string $"value")
    Do
      Delete "params" Where ("key" = $"key");;
      Insert "params" ($"key", $"value");;
      Response Success
        Message "Parameter set."
        Body ignore
      end
    end;;

    RosCommand "setParam"(!string $"caller_id", !string $"key", !int $"value")
    Do
      Delete "params" Where ("key" = $"key");;
      Insert "params" ($"key", $"value");;
      Response Success
        Message "Parameter set."
        Body ignore
      end
    end;;

    RosCommand "getParamNames"(!string $"caller_id")
    Do
      Response Success
        Message "Parameter names are:"
        Body
          ArrayFrom "params" Write
            !string "params"#"key"
      end
    end
  )%program.

  Theorem Wf : wf ts pr buf_size.
    wf.
  Qed.

  Definition port : W := 11311%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).
