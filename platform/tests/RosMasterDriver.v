Require Import Ros XmlProg.

Module M.
  Definition buf_size := 1024%N.
  Definition heapSize := (1024 * 1024 * 25)%N.

  Definition dbaddr (n : nat) := ((heapSize + 50 + 2 + N.of_nat n) * 4)%N.

  Definition ts :=
    {| Name := "params";
      Address := dbaddr 0;
      Schema := "key" :: "value" :: nil
    |}
    :: {| Name := "nodes";
      Address := dbaddr 1;
      Schema := "caller_id" :: "caller_api" :: nil
    |}
    :: {| Name := "services";
      Address := dbaddr 2;
      Schema := "service" :: "service_api" :: nil
    |}
    :: nil.

  Definition registerNode := (
    Delete "nodes" Where ("caller_id" = $"caller_id");;
    Insert "nodes" ($"caller_id", $"caller_api")
  )%action.

  Definition pr := (
    (** * Parameter server <http://www.ros.org/wiki/ROS/Parameter_Server_API> *)

    (* Remove a parameter setting. *)
    RosCommand "deleteParam"(!string $"caller_id", !string $"key")
    Do
      Delete "params" Where ("key" = $"key");;
      Response Success
        Message "Parameter deleted."
        Body ignore
      end
    end;;

    (* Set the value of a parameter. *)
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

    (* Get the value of a parameter. *)
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

    (* Search for a parameter name relative to the caller's namespace. *)
    Unimplemented "searchParam"(!string $"caller_id", !string $"key");;

    (* Sign up to receive notifications when a parameter value changes. *)
    Unimplemented "subscribeParam"(!string $"caller_id", !string $"caller_api", !string $"key");;

    (* Cancel a subscription. *)
    Unimplemented "unsubscribeParam"(!string $"caller_id", !string $"caller_api", !string $"key");;

    (* Check if a parameter has a value. *)
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

    (* List all parameters that are set. *)
    RosCommand "getParamNames"(!string $"caller_id")
    Do
      Response Success
        Message "Parameter names are:"
        Body
          ArrayFrom "params" Write
            !string "params"#"key"
      end
    end;;


    (** * Master <http://www.ros.org/wiki/ROS/Master_API> *)

    (** ** Register/unregister *)

    (* Announce willingness to provide a service. *)
    RosCommand "registerService"(!string $"caller_id", !string $"service",
      !string $"service_api", !string $"caller_api")
    Do
      IfHas "services" Where ("service" = $"service") then
        Response UserError
          Message "That service is already being provided."
          Body ignore
        end
      else
        registerNode;;
        Insert "services" ($"service", $"service_api");;
        Response Success
          Message "Service registered."
          Body ignore
        end
      end
    end;;

    (* Rescind willingness to provide a service. *)
    RosCommand "unregisterService"(!string $"caller_id", !string $"service",
      !string $"service_api")
    Do
      IfHas "services" Where ("service" = $"service") then
        Delete "services" Where ("service" = $"service");;
        Response Success
          Message "Service unregistered."
          Body !int "1"
        end
      else
        Response Success
          Message "Service was not registered in the first place."
          Body !int "0"
        end
      end
    end;;

    (* Register intent to publish on a topic. *)
    Unimplemented "registerPublisher"(!string $"caller_id", !string $"topic",
      !string $"topic_type", !string $"caller_api");;

    (* Unregister intent to publish on a topic. *)
    Unimplemented "unregisterPublisher"(!string $"caller_id", !string $"topic",
      !string $"caller_api");;


    (** ** Name service and system state *)

    (* Get the XML-RPC URI for a node name. *)
    Unimplemented "lookupNode"(!string $"caller_id", !string $"node_name");;

    (* List published topics in a particular namespace. *)
    Unimplemented "getPublishedTopics"(!string $"caller_id", !string $"subgraph");;

    (* List all known topic types. *)
    Unimplemented "getTopicTypes"(!string $"caller_id");;

    (* Dump of all relevant service/topic state. *)
    Unimplemented "getSystemState"(!string $"caller_id");;

    (* Get the master's URI. *)
    RosCommand "getUri"(!string $"caller_id")
    Do
      Response Success
        Message "My URI is:"
        Body !string "http://localhost:11311"
      end
    end;;

    (* Find the node providing a service. *)
    RosCommand "lookupService"(!string $"caller_id", !string $"service")
    Do
      IfHas "services" Where ("service" = $"service") then
        Response Success
          Message "Service provider is:"
          Body
            From "services" Where ("service" = $"service") Write
              !string "services"#"service_api"
        end
      else
        Response UserError
          Message "No one is providing that service."
          Body ignore
        end
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
