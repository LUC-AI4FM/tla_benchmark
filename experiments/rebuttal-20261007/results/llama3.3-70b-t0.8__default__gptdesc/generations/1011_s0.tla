```
MODULE KeyValueStore
EXTENDS Integers, FiniteSets

CONSTANTS Keys, Vals
VARIABLES store, op, key, val, rval, rd, ready

Init == 
  /\ store = [k \in Keys |-> MISSING]
  /\ op = "idle"
  /\ key = NULL
  /\ val = NULL
  /\ rval = NULL
  /\ rd = FALSE
  /\ ready = TRUE

Next == 
  IF ready THEN
    (
      /\ op' = "get"
      /\ key' \in Keys
      /\ val' = NULL
      /\ rval' = store[key']
      /\ rd' = TRUE
      /\ ready' = FALSE
    )
    OR 
    (
      /\ op' = "insert"
      /\ key' \in Keys
      /\ val' \in Vals
      /\ rval' = NULL
      /\ rd' = FALSE
      /\ ready' = FALSE
    )
    OR 
    (
      /\ op' = "update"
      /\ key' \in Keys
      /\ val' \in Vals
      /\ rval' = NULL
      /\ rd' = FALSE
      /\ ready' = FALSE
    )
    OR 
    (
      /\ op' = "delete"
      /\ key' \in Keys
      /\ val' = NULL
      /\ rval' = NULL
      /\ rd' = FALSE
      /\ ready' = FALSE
    )
  ELSE 
    (
      /\ op = "get"
      /\ store' = store
      /\ op' = "idle"
      /\ key' = NULL
      /\ val' = NULL
      /\ rval' = NULL
      /\ rd' = FALSE
      /\ ready' = TRUE
    )
    OR 
    (
      /\ op = "insert"
      /\ store' = [store EXCEPT ![key] = val]
      /\ op' = "idle"
      /\ key' = NULL
      /\ val' = NULL
      /\ rval' = NULL
      /\ rd' = FALSE
      /\ ready' = TRUE
    )
    OR 
    (
      /\ op = "update"
      /\ store' = [store EXCEPT ![key] = val]
      /\ op' = "idle"
      /\ key' = NULL
      /\ val' = NULL
      /\ rval' = NULL
      /\ rd' = FALSE
      /\ ready' = TRUE
    )
    OR 
    (
      /\ op = "delete"
      /\ store' = [store EXCEPT ![key] = MISSING]
      /\ op' = "idle"
      /\ key' = NULL
      /\ val' = NULL
      /\ rval' = NULL
      /\ rd' = FALSE
      /\ ready' = TRUE
    )

Spec == 
  Init /\ [][Next]_<<store, op, key, val, rval, rd, ready>>
  /\ WF_(op = "delete")([][Next]_<<store, op, key, val, rval, rd, ready>>)

THEOREM Spec => []Init
```