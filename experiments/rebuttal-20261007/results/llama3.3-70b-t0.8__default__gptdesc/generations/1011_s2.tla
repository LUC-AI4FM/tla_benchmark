```
MODULE KeyValueStore

EXTENDS Integers, FiniteSets

CONSTANTS Keys, Vals
VARIABLES store, op, key, val, ret, ready

Init == (
  /\ store = [k \in Keys |-> MISSING]
  /\ op = "None"
  /\ key = NULL
  /\ val = NULL
  /\ ret = NULL
  /\ ready = TRUE
)

GetRequest == (
  /\ op = "Get"
  /\ key \in Keys
  /\ ready = FALSE
)

GetResponse == (
  /\ op = "Get"
  /\ ret = IF store[key] = MISSING THEN MISSING ELSE store[key]
  /\ ready = TRUE
  /\ UNCHANGED <<store, op, key, val>>
)

InsertRequest == (
  /\ op = "Insert"
  /\ key \in Keys
  /\ val \in Vals
  /\ ready = FALSE
)

InsertResponse == (
  /\ op = "Insert"
  /\ store' = [store EXCEPT ![key] = val]
  /\ ret = val
  /\ ready = TRUE
  /\ UNCHANGED <<op, key, val>>
)

UpdateRequest == (
  /\ op = "Update"
  /\ key \in Keys
  /\ val \in Vals
  /\ store[key] /= MISSING
  /\ ready = FALSE
)

UpdateResponse == (
  /\ op = "Update"
  /\ store' = [store EXCEPT ![key] = val]
  /\ ret = val
  /\ ready = TRUE
  /\ UNCHANGED <<op, key, val>>
)

DeleteRequest == (
  /\ op = "Delete"
  /\ key \in Keys
  /\ ready = FALSE
)

DeleteResponse == (
  /\ op = "Delete"
  /\ store' = [store EXCEPT ![key] = MISSING]
  /\ ret = "Deleted"
  /\ ready = TRUE
  /\ UNCHANGED <<op, key, val>>
)

NoOp == (
  /\ ready = TRUE
  /\ UNCHANGED <<store, op, key, val, ret, ready>>
)

Next == (
  \/ (GetRequest /\ GetResponse)
  \/ (InsertRequest /\ InsertResponse)
  \/ (UpdateRequest /\ UpdateResponse)
  \/ (DeleteRequest /\ DeleteResponse)
  \/ NoOp
)

Spec == (
  Init /\ [][Next]_<<store, op, key, val, ret, ready>>
  /\ WF_(DeleteRequest)(op = "Delete")
)

THEOREM Spec => []Init

TypeOK == (
  store \in [Keys -> (Vals \cup {MISSING})]
  /\ op \in {"None", "Get", "Insert", "Update", "Delete"}
  /\ key \in Keys \cup {NULL}
  /\ val \in Vals \cup {NULL}
  /\ ret \in (Vals \cup {MISSING, "Deleted"}) \cup {NULL}
  /\ ready \in BOOLEAN
)

Inv == TypeOK

THEOREM Spec => []Inv
```