Require Import Ros XmlProg.

Module M.
  Definition buf_size := 1024%N.
  Definition heapSize := (1024 * 1024 * 25)%N.

  Definition ts := {| Name := "params";
    Address := ((heapSize + 50 + 2) * 4)%N;
    Schema := "key" :: "value" :: nil
  |} :: nil.

  Definition pr := (
    RosCommand "deleteParam"(!string $"caller_id", !string $"key")
    Do
      Delete "params" Where ("key" = $"key");;
      Response Success
        Message "Parameter deleted."
        Body ignore
      end
    end;;

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

    RosCommand "getParam"(!string $"caller_id", !string $"key")
    Do
      IfHas "params" Where ("key" = $"key") then
        Response Success
          Message "Parameter value is:"
          Body
            From "params" Where ("key" = $"key") Write
              !string "params"#"value"
        end
      else
        Response UserError
          Message "Parameter not found."
          Body ignore
        end
      end
    end;;

    RosCommand "hasParam"(!string $"caller_id", !string $"key")
    Do
      IfHas "params" Where ("key" = $"key") then
        Response Success
          Message "Parameter is set."
          Body !true
        end
      else
        Response Success
          Message "Parameter is not set."
          Body !false
        end
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
