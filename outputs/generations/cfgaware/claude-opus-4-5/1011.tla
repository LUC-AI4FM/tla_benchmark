---------------------------- MODULE KeyValueStore ----------------------------

CONSTANTS Keys, Vals, MISSING

VARIABLES store, op, args, result, state

vars == <<store, op, args, result, state>>

TypeOK ==
    /\ store \in [Keys -> Vals \cup {MISSING}]
    /\ op \in {"get", "insert", "update", "delete", "none"}
    /\ args \in [key: Keys, val: Vals \cup {MISSING}]
    /\ result \in Vals \cup {MISSING, "ok", "error", "none"}
    /\ state \in {"ready", "working"}

Init ==
    /\ store = [k \in Keys |-> MISSING]
    /\ op = "none"
    /\ args = [key |-> CHOOSE k \in Keys : TRUE, val |-> MISSING]
    /\ result = "none"
    /\ state = "ready"

GetRequest(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = [key |-> k, val |-> MISSING]
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

GetResponse ==
    /\ state = "working"
    /\ op = "get"
    /\ result' = store[args.key]
    /\ state' = "ready"
    /\ op' = "none"
    /\ UNCHANGED <<store, args>>

InsertRequest(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = [key |-> k, val |-> v]
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

InsertResponse ==
    /\ state = "working"
    /\ op = "insert"
    /\ IF store[args.key] = MISSING
       THEN /\ store' = [store EXCEPT ![args.key] = args.val]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ state' = "ready"
    /\ op' = "none"
    /\ UNCHANGED args

UpdateRequest(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = [key |-> k, val |-> v]
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

UpdateResponse ==
    /\ state = "working"
    /\ op = "update"
    /\ IF store[args.key] # MISSING
       THEN /\ store' = [store EXCEPT ![args.key] = args.val]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ state' = "ready"
    /\ op' = "none"
    /\ UNCHANGED args

DeleteRequest(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = [key |-> k, val |-> MISSING]
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

DeleteResponse ==
    /\ state = "working"
    /\ op = "delete"
    /\ IF store[args.key] # MISSING
       THEN /\ store' = [store EXCEPT ![args.key] = MISSING]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ state' = "ready"
    /\ op' = "none"
    /\ UNCHANGED args

Request ==
    \/ \E k \in Keys : GetRequest(k)
    \/ \E k \in Keys, v \in Vals : InsertRequest(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateRequest(k, v)
    \/ \E k \in Keys : DeleteRequest(k)

Response ==
    \/ GetResponse
    \/ InsertResponse
    \/ UpdateResponse
    \/ DeleteResponse

Next == Request \/ Response

DeleteRequestAction == \E k \in Keys : DeleteRequest(k)

Spec == Init /\ [][Next]_vars /\ WF_op(DeleteRequestAction)

=============================================================================