---- MODULE KVStore ----
EXTENDS TLC

CONSTANTS Keys, Vals, NIL, MISSING

ASSUME MISSING \notin Vals
ASSUME NIL \notin Vals
ASSUME NIL # MISSING
ASSUME MISSING \notin {"get", "insert", "update", "delete"}
ASSUME NIL \notin {"get", "insert", "update", "delete"}

VARIABLES op, args, ret, dict, state

vars == <<op, args, ret, dict, state>>

Ops == {"get", "insert", "update", "delete"}

TypeOK ==
    /\ op \in Ops \cup {NIL}
    /\ args \in {<<k>> : k \in Keys} \cup {<<k, v>> : k \in Keys, v \in Vals} \cup {NIL}
    /\ ret \in Vals \cup {MISSING, NIL, "ok", "error"}
    /\ dict \in [Keys -> Vals \cup {MISSING}]
    /\ state \in {"ready", "working"}

Init ==
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ dict = [k \in Keys |-> MISSING]
    /\ state = "ready"

\* Requests

GetReq(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<k>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

InsertReq(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

UpdateReq(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

DeleteReq(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = <<k>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

\* Responses

GetResp ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = dict[args[1]]
    /\ state' = "ready"
    /\ UNCHANGED <<op, args, dict>>

InsertResp ==
    /\ state = "working"
    /\ op = "insert"
    /\ LET k == args[1]
           v == args[2]
       IN IF dict[k] = MISSING
            THEN /\ dict' = [dict EXCEPT ![k] = v]
                 /\ ret' = "ok"
            ELSE /\ ret' = "error"
                 /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

UpdateResp ==
    /\ state = "working"
    /\ op = "update"
    /\ LET k == args[1]
           v == args[2]
       IN IF dict[k] = MISSING
            THEN /\ ret' = "error"
                 /\ UNCHANGED dict
            ELSE /\ dict' = [dict EXCEPT ![k] = v]
                 /\ ret' = "ok"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

DeleteResp ==
    /\ state = "working"
    /\ op = "delete"
    /\ dict' = [dict EXCEPT ![args[1]] = MISSING]
    /\ ret' = "ok"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

DeleteRequest == \E k \in Keys : DeleteReq(k)

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ DeleteRequest
    \/ GetResp
    \/ InsertResp
    \/ UpdateResp
    \/ DeleteResp

Spec == Init /\ [][Next]_vars /\ WF_vars(DeleteRequest)

====