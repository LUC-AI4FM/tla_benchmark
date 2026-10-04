-------------------------------- MODULE KeyValueStore --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Keys, Vals, MISSING

VARIABLES store, state, op, args, result

vars == <<store, state, op, args, result>>

TypeOK ==
    /\ store \in [Keys -> Vals \cup {MISSING}]
    /\ state \in {"ready", "working"}
    /\ op \in {"get", "insert", "update", "delete", "none"}
    /\ args \in [key: Keys \cup {MISSING}, val: Vals \cup {MISSING}]
    /\ result \in Vals \cup {MISSING, "ok", "error", "none"}

Init ==
    /\ store = [k \in Keys |-> MISSING]
    /\ state = "ready"
    /\ op = "none"
    /\ args = [key |-> MISSING, val |-> MISSING]
    /\ result = "none"

\* Get operation
GetRequest(k) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "get"
    /\ args' = [key |-> k, val |-> MISSING]
    /\ result' = "none"
    /\ UNCHANGED store

GetResponse ==
    /\ state = "working"
    /\ op = "get"
    /\ args.key \in Keys
    /\ result' = store[args.key]
    /\ state' = "ready"
    /\ op' = "none"
    /\ args' = [key |-> MISSING, val |-> MISSING]
    /\ UNCHANGED store

\* Insert operation
InsertRequest(k, v) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "insert"
    /\ args' = [key |-> k, val |-> v]
    /\ result' = "none"
    /\ UNCHANGED store

InsertResponse ==
    /\ state = "working"
    /\ op = "insert"
    /\ args.key \in Keys
    /\ args.val \in Vals
    /\ IF store[args.key] = MISSING
       THEN /\ store' = [store EXCEPT ![args.key] = args.val]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ state' = "ready"
    /\ op' = "none"
    /\ args' = [key |-> MISSING, val |-> MISSING]

\* Update operation
UpdateRequest(k, v) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "update"
    /\ args' = [key |-> k, val |-> v]
    /\ result' = "none"
    /\ UNCHANGED store

UpdateResponse ==
    /\ state = "working"
    /\ op = "update"
    /\ args.key \in Keys
    /\ args.val \in Vals
    /\ IF store[args.key] # MISSING
       THEN /\ store' = [store EXCEPT ![args.key] = args.val]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ state' = "ready"
    /\ op' = "none"
    /\ args' = [key |-> MISSING, val |-> MISSING]

\* Delete operation
DeleteRequest(k) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "delete"
    /\ args' = [key |-> k, val |-> MISSING]
    /\ result' = "none"
    /\ UNCHANGED store

DeleteResponse ==
    /\ state = "working"
    /\ op = "delete"
    /\ args.key \in Keys
    /\ IF store[args.key] # MISSING
       THEN /\ store' = [store EXCEPT ![args.key] = MISSING]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ state' = "ready"
    /\ op' = "none"
    /\ args' = [key |-> MISSING, val |-> MISSING]

\* Combined request action for delete (for fairness)
DeleteRequestAction ==
    \E k \in Keys : DeleteRequest(k)

Next ==
    \/ \E k \in Keys : GetRequest(k)
    \/ GetResponse
    \/ \E k \in Keys, v \in Vals : InsertRequest(k, v)
    \/ InsertResponse
    \/ \E k \in Keys, v \in Vals : UpdateRequest(k, v)
    \/ UpdateResponse
    \/ \E k \in Keys : DeleteRequest(k)
    \/ DeleteResponse

Spec == Init /\ [][Next]_vars /\ WF_op(DeleteRequestAction)

\* Safety invariant: Type correctness is always maintained
Safety == TypeOK

\* Liveness property: If a delete is requested, eventually the system returns to ready
DeleteEventuallyCompletes ==
    (op = "delete" /\ state = "working") ~> (state = "ready")

================================================================================