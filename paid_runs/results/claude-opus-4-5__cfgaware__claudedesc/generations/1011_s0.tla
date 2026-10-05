-------------------------------- MODULE kv_store --------------------------------

CONSTANTS Keys, Vals, MISSING, NIL

VARIABLES op, args, ret, dict, state

vars == <<op, args, ret, dict, state>>

Operations == {"get", "insert", "update", "delete"}

TypeOK ==
    /\ op \in Operations \cup {NIL}
    /\ args \in (Keys \cup (Keys \times Vals) \cup {NIL})
    /\ ret \in (Vals \cup {"ok", "error", MISSING, NIL})
    /\ dict \in [Keys -> Vals \cup {MISSING}]
    /\ state \in {"ready", "working"}

Init ==
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ dict = [k \in Keys |-> MISSING]
    /\ state = "ready"

GetRequest(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = k
    /\ ret' = ret
    /\ dict' = dict
    /\ state' = "working"

GetResponse ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = dict[args]
    /\ op' = NIL
    /\ args' = NIL
    /\ dict' = dict
    /\ state' = "ready"

InsertRequest(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ ret' = ret
    /\ dict' = dict
    /\ state' = "working"

InsertResponse ==
    /\ state = "working"
    /\ op = "insert"
    /\ LET k == args[1]
           v == args[2]
       IN IF dict[k] = MISSING
          THEN /\ dict' = [dict EXCEPT ![k] = v]
               /\ ret' = "ok"
          ELSE /\ dict' = dict
               /\ ret' = "error"
    /\ op' = NIL
    /\ args' = NIL
    /\ state' = "ready"

UpdateRequest(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ ret' = ret
    /\ dict' = dict
    /\ state' = "working"

UpdateResponse ==
    /\ state = "working"
    /\ op = "update"
    /\ LET k == args[1]
           v == args[2]
       IN IF dict[k] # MISSING
          THEN /\ dict' = [dict EXCEPT ![k] = v]
               /\ ret' = "ok"
          ELSE /\ dict' = dict
               /\ ret' = "error"
    /\ op' = NIL
    /\ args' = NIL
    /\ state' = "ready"

DeleteRequest(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = k
    /\ ret' = ret
    /\ dict' = dict
    /\ state' = "working"

DeleteResponse ==
    /\ state = "working"
    /\ op = "delete"
    /\ dict' = [dict EXCEPT ![args] = MISSING]
    /\ ret' = "ok"
    /\ op' = NIL
    /\ args' = NIL
    /\ state' = "ready"

DeleteRequestAction ==
    \E k \in Keys : DeleteRequest(k)

Next ==
    \/ \E k \in Keys : GetRequest(k)
    \/ GetResponse
    \/ \E k \in Keys, v \in Vals : InsertRequest(k, v)
    \/ InsertResponse
    \/ \E k \in Keys, v \in Vals : UpdateRequest(k, v)
    \/ UpdateResponse
    \/ DeleteRequestAction
    \/ DeleteResponse

Spec == Init /\ [][Next]_vars /\ WF_vars(DeleteRequestAction)

================================================================================