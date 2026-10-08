------------------------------- MODULE KeyValueStore -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Keys, Values
VARIABLES store, currentOp, argKey, argValue, result, processing

Init == /\ store = << >>
        /\ currentOp \in {"get", "insert", "update", "delete"} \/ currentOp = ""
        /\ argKey \in Keys \/ argKey = ""
        /\ argValue \in Values \/ argValue = ""
        /\ result \in {"missing", "ok", "error"} \/ result = ""
        /\ processing \in {TRUE, FALSE}

Next == \/ /\ ~processing
            /\ \/ /\ currentOp = "get"
                   /\ argKey \in Keys
                   /\ (argKey \notin DOMAIN store => result' = "missing")
                   /\ (argKey \in DOMAIN store => result' = store[argKey])
               \/ /\ currentOp = "insert"
                   /\ argKey \in Keys
                   /\ argValue \in Values
                   /\ (argKey \notin DOMAIN store => \/ store' = [store EXCEPT ![argKey] = argValue]
                                                            /\ result' = "ok")
                   /\ (argKey \in DOMAIN store => \/ store' = store
                                                            /\ result' = "error")
               \/ /\ currentOp = "update"
                   /\ argKey \in Keys
                   /\ argValue \in Values
                   /\ (argKey \in DOMAIN store => \/ store' = [store EXCEPT ![argKey] = argValue]
                                                            /\ result' = "ok")
                   /\ (argKey \notin DOMAIN store => \/ store' = store
                                                            /\ result' = "error")
               \/ /\ currentOp = "delete"
                   /\ argKey \in Keys
                   /\ (argKey \in DOMAIN store => \/ store' = [store EXCEPT !<<argKey>>])
                   /\ (argKey \notin DOMAIN store => \/ store' = store)
                   /\ result' = "ok"
            /\ processing'
        \/ /\ processing
            /\ currentOp' = ""
            /\ argKey' = ""
            /\ argValue' = ""
            /\ result' = ""
            /\ processing' = FALSE

Spec == Init /\ [][Next]_<<store, currentOp, argKey, argValue, result, processing>>

TypeOK == /\ store \in [Keys -> Values]
          /\ currentOp \in {"get", "insert", "update", "delete"} \/ currentOp = ""
          /\ argKey \in Keys \/ argKey = ""
          /\ argValue \in Values \/ argValue = ""
          /\ result \in {"missing", "ok", "error"} \/ result = ""
          /\ processing \in {TRUE, FALSE}

FairDelete == WF_<<store, currentOp, argKey, argValue, result, processing>> (currentOp = "delete")

THEOREM Spec => []TypeOK
THEOREM Spec => FairDelete
=============================================================================