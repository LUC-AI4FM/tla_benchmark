```tla
MODULE KeyValueStore

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Keys, Vals
VARIABLES store, op, arg1, arg2, ret, ready

(* --algorithm KeyValueStore

variables 
    store = [k \in Keys |-> "MISSING"],
    op = "idle",
    arg1 = <<>>,
    arg2 = <<>>,
    ret = <<>>,
    ready = TRUE;

Init == /\ store \in [Keys -> {"MISSING"} \cup Vals]
        /\ op = "idle"
        /\ arg1 = <<>>
        /\ arg2 = <<>>
        /\ ret = <<>>
        /\ ready = TRUE

Next ==
    \/ /\ ready
       /\ \/ \/ /\ op = "get"
                 /\ arg1 \in Keys
                 /\ (store[arg1] = "MISSING" -> ret = "MISSING")
                    \/ store[arg1] \in Vals -> ret = store[arg1]
              \/ /\ op = "insert"
                 /\ arg1 \in Keys
                 /\ arg2 \in Vals
                 /\ ready'
                 /\ store' = [store EXCEPT ![arg1] = arg2]
                 /\ ret' = <<>>
              \/ /\ op = "update"
                 /\ arg1 \in Keys
                 /\ arg2 \in Vals
                 /\ (store[arg1] = "MISSING" -> ret = FALSE)
                    \/ store[arg1] \in Vals -> /\ ready'
                                                 /\ store' = [store EXCEPT ![arg1] = arg2]
                                                 /\ ret' = TRUE
              \/ /\ op = "delete"
                 /\ arg1 \in Keys
                 /\ (store[arg1] = "MISSING" -> ret = FALSE)
                    \/ store[arg1] \in Vals -> /\ ready'
                                                 /\ store' = [store EXCEPT ![arg1] = "MISSING"]
                                                 /\ ret' = TRUE
       /\ op' = "idle"
       /\ arg1' = <<>>
       /\ arg2' = <<>>
       /\ ready' = FALSE

    \/ /\ \neg ready
       /\ op = "idle"
       /\ op' \in {"get", "insert", "update", "delete"}
       /\ arg1' \in Keys
       /\ (op' \in {"get"} -> arg2' = <<>>)
          \/ (op' \in {"insert", "update"} -> arg2' \in Vals)
          \/ (op' \in {"delete"} -> arg2' = <<>>)
       /\ ret' = <<>>
       /\ ready'

Spec ==
    /\ Init
    /\ [][Next]_<<store, op, arg1, arg2, ret, ready>>
    /\ WF_next(<<store, op, arg1, arg2, ret, ready>>, {op \in {"delete"}})

==*)
```