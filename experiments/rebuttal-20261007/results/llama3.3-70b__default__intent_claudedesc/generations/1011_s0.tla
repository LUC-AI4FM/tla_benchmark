```
MODULE KeyValueStore
EXTENDS Integers, FiniteSets

CONSTANTS Keys, Values
VARIABLES store, op, argKey, argValue, result, processing

Init ==
  /\ store = []
  /\ op = "none"
  /\ argKey = "none"
  /\ argValue = "none"
  /\ result = "none"
  /\ processing = "idle"

Next ==
  \/ (op = "get" /\ processing = "idle")
      /\ E k \in Keys : 
        /\ argKey = k
        /\ IF k \in DOMAIN store THEN result = store[k] ELSE result = "missing"
        /\ op = "done"
        /\ processing = "done"
  \/ (op = "insert" /\ processing = "idle")
      /\ E k \in Keys, v \in Values :
        /\ argKey = k
        /\ argValue = v
        /\ IF k \notin DOMAIN store THEN 
            /\ store = [store EXCEPT ![k] = v]
            /\ result = "ok"
          ELSE
            /\ result = "error"
        /\ op = "done"
        /\ processing = "done"
  \/ (op = "update" /\ processing = "idle")
      /\ E k \in Keys, v \in Values :
        /\ argKey = k
        /\ argValue = v
        /\ IF k \in DOMAIN store THEN 
            /\ store = [store EXCEPT ![k] = v]
            /\ result = "ok"
          ELSE
            /\ result = "error"
        /\ op = "done"
        /\ processing = "done"
  \/ (op = "delete" /\ processing = "idle")
      /\ E k \in Keys :
        /\ argKey = k
        /\ store = [x \in DOMAIN store |-> v \in Values : x /= k]
        /\ result = "ok"
        /\ op = "done"
        /\ processing = "done"
  \/ (processing = "idle")
      /\ op = "none"
      /\ argKey = "none"
      /\ argValue = "none"
      /\ result = "none"

TypeCorrectness ==
  /\ store \in [Keys -> Values]
  /\ op \in {"none", "get", "insert", "update", "delete", "done"}
  /\ argKey \in Keys \cup {"none"}
  /\ argValue \in Values \cup {"none"}
  /\ result \in (Values \cup {"missing", "ok", "error"})
  /\ processing \in {"idle", "done"}

Spec ==
  /\ Init
  /\ [][Next]_store
  /\ WF_vars(Next, store)

THEOREM Spec => []TypeCorrectness
```