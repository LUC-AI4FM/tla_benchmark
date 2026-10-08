------------------------------- MODULE KeyValueStore -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS Keys, Vals
VARIABLES store, op, arg1, arg2, result, ready

Init == /\ store = [k \in Keys |-> "MISSING"]
        /\ op = "none"
        /\ arg1 = <<>>
        /\ arg2 = <<>>
        /\ result = "undefined"
        /\ ready = TRUE

Next ==
    \/ /\ ready
       /\ op = "get"
       /\ arg1 \in Keys
       /\ ~ (arg1 \in DOMAIN store)
       /\ result' = "MISSING"
       /\ op' = "none"
       /\ ready'
       \/ /\ ready
          /\ op = "get"
          /\ arg1 \in Keys
          /\ arg1 \in DOMAIN store
          /\ result' = store[arg1]
          /\ op' = "none"
          /\ ready'
       \/ /\ ready
          /\ op = "insert"
          /\ arg1 \in Keys
          /\ arg2 \in Vals
          /\ store' = [store EXCEPT ![arg1] = arg2]
          /\ result' = "ok"
          /\ op' = "none"
          /\ ready'
       \/ /\ ready
          /\ op = "update"
          /\ arg1 \in Keys
          /\ arg2 \in Vals
          /\ arg1 \in DOMAIN store
          /\ store' = [store EXCEPT ![arg1] = arg2]
          /\ result' = "ok"
          /\ op' = "none"
          /\ ready'
       \/ /\ ready
          /\ op = "delete"
          /\ arg1 \in Keys
          /\ arg1 \in DOMAIN store
          /\ store' = [store EXCEPT ![arg1] = "MISSING"]
          /\ result' = "ok"
          /\ op' = "none"
          /\ ready'
       \/ /\ ~ready
          /\ op' \in {"get", "insert", "update", "delete"}
          /\ arg1' \in Keys
          /\ (op' \notin {"insert", "update", "delete"} \/ arg2' \in Vals)
          /\ result' = "undefined"
          /\ ready'

Spec ==
    Init /\ [][Next]_<<store, op, arg1, arg2, result, ready>> /\ WF_<<op>>_Next

================================================================================