------------------------------- MODULE KeyValueStore -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Keys, Vals
VARIABLES store, op, arg1, arg2, ret, ready

Init == /\ store = [k \in Keys |-> "MISSING"]
        /\ op = "idle"
        /\ arg1 \notin Keys
        /\ arg2 \notin Vals
        /\ ret \notin Vals \/ ret = "MISSING"
        /\ ready = TRUE

TypeOK == /\ store \in [Keys -> (Vals \cup {"MISSING"})]
          /\ op \in {"get", "insert", "update", "delete", "idle"}
          /\ arg1 \in Keys \/ op = "idle"
          /\ arg2 \in Vals \/ op \in {"get", "delete", "idle"}

Next == \/ /\ ready
            /\ op = "get"
            /\ arg1 \in Keys
            /\ ret' = store[arg1]
            /\ UNCHANGED <<store, op, arg1, arg2, ready>>
         \/ /\ ready
            /\ op = "insert"
            /\ arg1 \in Keys
            /\ arg2 \in Vals
            /\ store' = [store EXCEPT ![arg1] = arg2]
            /\ ret' = "OK"
            /\ UNCHANGED <<op, arg1, arg2, ready>>
         \/ /\ ready
            /\ op = "update"
            /\ arg1 \in Keys
            /\ arg2 \in Vals
            /\ store[arg1] \notin {"MISSING"}
            /\ store' = [store EXCEPT ![arg1] = arg2]
            /\ ret' = "OK"
            /\ UNCHANGED <<op, arg1, arg2, ready>>
         \/ /\ ready
            /\ op = "delete"
            /\ arg1 \in Keys
            /\ store[arg1] \notin {"MISSING"}
            /\ store' = [store EXCEPT ![arg1] = "MISSING"]
            /\ ret' = "OK"
            /\ UNCHANGED <<op, arg1, arg2, ready>>
         \/ /\ op \in {"get", "insert", "update", "delete"}
            /\ ready
            /\ op' = "idle"
            /\ arg1' \notin Keys
            /\ arg2' \notin Vals
            /\ ret' \notin Vals \/ ret' = "MISSING"
            /\ ready' = FALSE
         \/ /\ op = "idle"
            /\ \neg ready
            /\ op' \in {"get", "insert", "update", "delete"}
            /\ arg1' \in Keys
            /\ (op' \in {"insert", "update"} => arg2' \in Vals)
            /\ UNCHANGED <<store, ret, ready>>

Spec == Init /\ [][Next]_<<store, op, arg1, arg2, ret, ready>> /\ WF_next(<<op>>) 

WF_next(op) == <>(\E k \in Keys : op = "delete" /\ store[k] \notin {"MISSING"})
=============================================================================