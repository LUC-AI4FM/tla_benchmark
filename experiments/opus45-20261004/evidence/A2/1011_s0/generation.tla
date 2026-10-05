---------------------------- MODULE KeyValueStore ----------------------------

EXTENDS Sequences, TLC

CONSTANTS Keys, Vals, MISSING, NIL

ASSUME MISSING \notin Vals
ASSUME NIL \notin Vals
ASSUME NIL \notin {"get", "insert", "update", "delete"}
ASSUME MISSING \notin {"get", "insert", "update", "delete"}

VARIABLES op, args, ret, dict, state

vars == <<op, args, ret, dict, state>>

TypeOK ==
    /\ op \in {"get", "insert", "update", "delete"} \cup {NIL}
    /\ args \in ({Keys} \X (Vals \cup {NIL})) \cup {NIL}
    /\ ret \in Vals \cup {MISSING, "ok", "error", NIL}
    /\ dict \in [Keys -> Vals \cup {MISSING}]
    /\ state \in {"ready", "working"}

Init ==
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ dict \in [Keys -> {MISSING}]
    /\ state = "ready"

GetRequest(k) ==
    /\ state = "ready"
    /\ k \in Keys
    /\ op' = "get"
    /\ args' = <<k, NIL>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

GetResponse ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = dict[args[1]]
    /\ op' = NIL
    /\ args' = NIL
    /\ state' = "ready"
    /\ UNCHANGED dict

InsertRequest(k, v) ==
    /\ state = "ready"
    /\ k \in Keys
    /\ v \in Vals
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

InsertResponse ==
    /\ state = "working"
    /\ op = "insert"
    /\ IF dict[args[1]] = MISSING
       THEN /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
            /\ ret' = "ok"
       ELSE /\ ret' = "error"
            /\ UNCHANGED dict
    /\ op' = NIL
    /\ args' = NIL
    /\ state' = "ready"

UpdateRequest(k, v) ==
    /\ state = "ready"
    /\ k \in Keys
    /\ v \in Vals
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

UpdateResponse ==
    /\ state = "working"
    /\ op = "update"
    /\ IF dict[args[1]] # MISSING
       THEN /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
            /\ ret' = "ok"
       ELSE /\ ret' = "error"
            /\ UNCHANGED dict
    /\ op' = NIL
    /\ args' = NIL
    /\ state' = "ready"

DeleteRequest(k) ==
    /\ state = "ready"
    /\ k \in Keys
    /\ op' = "delete"
    /\ args' = <<k, NIL>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

DeleteResponse ==
    /\ state = "working"
    /\ op = "delete"
    /\ dict' = [dict EXCEPT ![args[1]] = MISSING]
    /\ ret' = "ok"
    /\ op' = NIL
    /\ args' = NIL
    /\ state' = "ready"

DeleteRequestAction == \E k \in Keys : DeleteRequest(k)

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

=============================================================================