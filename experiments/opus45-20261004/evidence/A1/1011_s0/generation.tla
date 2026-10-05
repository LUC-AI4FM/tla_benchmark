---------------------------- MODULE spec ----------------------------

EXTENDS Naturals, Sequences

CONSTANTS Keys, Vals, MISSING

VARIABLES store, op, args, result, state

vars == <<store, op, args, result, state>>

TypeOK ==
    /\ store \in [Keys -> Vals \cup {MISSING}]
    /\ op \in {"get", "insert", "update", "delete", "none"}
    /\ args \in (Keys \X Vals) \cup Keys \cup {<<>>}
    /\ result \in Vals \cup {MISSING, "ok", "error", "none"}
    /\ state \in {"ready", "working"}

Init ==
    /\ store = [k \in Keys |-> MISSING]
    /\ op = "none"
    /\ args = <<>>
    /\ result = "none"
    /\ state = "ready"

GetRequest(k) ==
    /\ state = "ready"
    /\ op = "none"
    /\ op' = "get"
    /\ args' = k
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

GetResponse ==
    /\ state = "working"
    /\ op = "get"
    /\ args \in Keys
    /\ result' = store[args]
    /\ op' = "none"
    /\ args' = <<>>
    /\ state' = "ready"
    /\ UNCHANGED store

InsertRequest(k, v) ==
    /\ state = "ready"
    /\ op = "none"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

InsertResponse ==
    /\ state = "working"
    /\ op = "insert"
    /\ args \in Keys \X Vals
    /\ LET k == args[1]
           v == args[2]
       IN IF store[k] = MISSING
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ result' = "ok"
          ELSE /\ result' = "error"
               /\ UNCHANGED store
    /\ op' = "none"
    /\ args' = <<>>
    /\ state' = "ready"

UpdateRequest(k, v) ==
    /\ state = "ready"
    /\ op = "none"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

UpdateResponse ==
    /\ state = "working"
    /\ op = "update"
    /\ args \in Keys \X Vals
    /\ LET k == args[1]
           v == args[2]
       IN IF store[k] # MISSING
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ result' = "ok"
          ELSE /\ result' = "error"
               /\ UNCHANGED store
    /\ op' = "none"
    /\ args' = <<>>
    /\ state' = "ready"

DeleteRequest(k) ==
    /\ state = "ready"
    /\ op = "none"
    /\ op' = "delete"
    /\ args' = k
    /\ state' = "working"
    /\ UNCHANGED <<store, result>>

DeleteResponse ==
    /\ state = "working"
    /\ op = "delete"
    /\ args \in Keys
    /\ IF store[args] # MISSING
       THEN /\ store' = [store EXCEPT ![args] = MISSING]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ op' = "none"
    /\ args' = <<>>
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

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_op(DeleteRequestAction)

=============================================================================