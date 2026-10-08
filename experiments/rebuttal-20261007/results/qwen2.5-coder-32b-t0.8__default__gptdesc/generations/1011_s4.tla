------------------------------- MODULE KeyValueStore --------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Keys, Vals
VARIABLES store, op, arg1, arg2, ret, ready

Init == /\ store = [k \in Keys |-> "MISSING"]
        /\ op = "none"
        /\ arg1 \in UNION {Keys, Vals}
        /\ arg2 \in UNION {Vals, {"MISSING"}}
        /\ ret \in UNION {Vals, {"MISSING"}, {"ERROR"}}
        /\ ready = TRUE

TypeOK == /\ store \in [Keys -> (Vals \/ {"MISSING"})]
          /\ op \in {"get", "insert", "update", "delete", "none"}
          /\ arg1 \in Keys
          /\ arg2 \in (Vals \/ {"MISSING"})
          /\ ret \in (Vals \/ {"MISSING"} \/ {"ERROR"})
          /\ ready \in BOOLEAN

Get == /\ op = "get"
       /\ \E val \in Vals \/ {"MISSING"}: store[arg1] = val
       /\ ret' = store[arg1]
       /\ op' = "none"
       /\ ready' = TRUE

Insert == /\ op = "insert"
          /\ store[arg1] = "MISSING"
          /\ store' = [store EXCEPT ![arg1] = arg2]
          /\ ret' = {"ERROR"}
          /\ op' = "none"
          /\ ready' = TRUE

Update == /\ op = "update"
          /\ store[arg1] \in Vals
          /\ store' = [store EXCEPT ![arg1] = arg2]
          /\ ret' = {"ERROR"}
          /\ op' = "none"
          /\ ready' = TRUE

Delete == /\ op = "delete"
          /\ store[arg1] \in Vals
          /\ store' = [store EXCEPT ![arg1] = "MISSING"]
          /\ ret' = {"ERROR"}
          /\ op' = "none"
          /\ ready' = TRUE

Next == \/ /\ op = "none"
           /\ ready
           /\ UNCHANGED <<store, ret>>
           /\ \/ op' \in {"get", "insert", "update", "delete"}
              /\ arg1' \in Keys
              /\ (op' = "get" \/ op' = "delete" /\ UNCHANGED arg2)
              /\ (op' \in {"insert", "update"} /\ arg2' \in Vals)
              /\ ready' = FALSE
        \/ /\ ~ready
           /\ CASE op = "get" -> Get
              [] op = "insert" -> Insert
              [] op = "update" -> Update
              [] op = "delete" -> Delete

Spec == Init /\ [][Next]_<<store, op, arg1, arg2, ret, ready>> /\ WF_next(<<op>>) 

=============================================================================