------------------------------- MODULE KeyValueStore ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Keys, Vals

VARIABLES store, op, arg1, arg2, ret, ready

Init == /\ store = [k \in Keys |-> "MISSING"]
        /\ op = "idle"
        /\ arg1 \in Keys
        /\ arg2 \in Vals \/ arg2 = "MISSING"
        /\ ret = "undefined"
        /\ ready = TRUE

Next ==
    \/ /\ ready
       /\ op = "get"
       /\ store' = store
       /\ arg1' = arg1
       /\ arg2' = arg2
       /\ ret' = store[arg1]
       /\ ready' = FALSE
       /\ UNCHANGED <<op, arg2>>
    \/ /\ ready
       /\ op = "insert"
       /\ store' = [store EXCEPT ![arg1] = arg2]
       /\ arg1' = arg1
       /\ arg2' = arg2
       /\ ret' = "OK"
       /\ ready' = FALSE
       /\ UNCHANGED <<op>>
    \/ /\ ready
       /\ op = "update"
       /\ store[arg1] # "MISSING"
       /\ store' = [store EXCEPT ![arg1] = arg2]
       /\ arg1' = arg1
       /\ arg2' = arg2
       /\ ret' = "OK"
       /\ ready' = FALSE
       /\ UNCHANGED <<op>>
    \/ /\ ready
       /\ op = "delete"
       /\ store[arg1] # "MISSING"
       /\ store' = [store EXCEPT ![arg1] = "MISSING"]
       /\ arg1' = arg1
       /\ arg2' = arg2
       /\ ret' = "OK"
       /\ ready' = FALSE
       /\ UNCHANGED <<op>>
    \/ /\ \neg ready
       /\ store' = store
       /\ op' = op
       /\ arg1' = arg1
       /\ arg2' = arg2
       /\ ret' = ret
       /\ ready' = TRUE

Spec ==
    /\ Init
    /\ [][Next]_<<store, op, arg1, arg2, ret, ready>>
    /\ WF_<<op>> (/\ ready /\ op = "delete")

=============================================================================