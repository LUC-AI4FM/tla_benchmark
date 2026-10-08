```
MODULE KeyValueStore
EXTENDS Integers, TLC

CONSTANTS Keys, Vals
VARIABLES store, op, key, val, returnVal, ready

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ op = "None"
  /\ key = NULL
  /\ val = NULL
  /\ returnVal = NULL
  /\ ready = TRUE

TypeCorrectness ==
  /\ store \in [Keys -> Vals \cup {MISSING}]
  /\ op \in {"None", "Get", "Insert", "Update", "Delete"}
  /\ key \in Keys \cup {NULL}
  /\ val \in Vals \cup {NULL}
  /\ returnVal \in Vals \cup {MISSING, NULL}

GetRequest ==
  /\ op = "None"
  /\ ready = TRUE
  /\ op' = "Get"
  /\ key' \in Keys
  /\ val' = NULL
  /\ returnVal' = NULL
  /\ ready' = FALSE
  /\ UNCHANGED store

GetResponse ==
  /\ op = "Get"
  /\ op' = "None"
  /\ key' = NULL
  /\ val' = NULL
  /\ returnVal' = IF store[key] = MISSING THEN MISSING ELSE store[key]
  /\ ready' = TRUE
  /\ UNCHANGED store

InsertRequest ==
  /\ op = "None"
  /\ ready = TRUE
  /\ op' = "Insert"
  /\ key' \in Keys
  /\ val' \in Vals
  /\ returnVal' = NULL
  /\ ready' = FALSE
  /\ UNCHANGED store

InsertResponse ==
  /\ op = "Insert"
  /\ op' = "None"
  /\ key' = NULL
  /\ val' = NULL
  /\ returnVal' = val
  /\ store' = [store EXCEPT ![key] = val]
  /\ ready' = TRUE

UpdateRequest ==
  /\ op = "None"
  /\ ready = TRUE
  /\ op' = "Update"
  /\ key' \in Keys
  /\ val' \in Vals
  /\ returnVal' = NULL
  /\ ready' = FALSE
  /\ UNCHANGED store

UpdateResponse ==
  /\ op = "Update"
  /\ op' = "None"
  /\ key' = NULL
  /\ val' = NULL
  /\ returnVal' = IF store[key] = MISSING THEN MISSING ELSE val
  /\ store' = [store EXCEPT ![key] = val]
  /\ ready' = TRUE

DeleteRequest ==
  /\ op = "None"
  /\ ready = TRUE
  /\ op' = "Delete"
  /\ key' \in Keys
  /\ val' = NULL
  /\ returnVal' = NULL
  /\ ready' = FALSE
  /\ UNCHANGED store

DeleteResponse ==
  /\ op = "Delete"
  /\ op' = "None"
  /\ key' = NULL
  /\ val' = NULL
  /\ returnVal' = MISSING
  /\ store' = [store EXCEPT ![key] = MISSING]
  /\ ready' = TRUE

Next ==
  \/ GetRequest
  \/ GetResponse
  \/ InsertRequest
  \/ InsertResponse
  \/ UpdateRequest
  \/ UpdateResponse
  \/ DeleteRequest
  \/ DeleteResponse
  \/ (UNCHANGED <<op, key, val, returnVal, store, ready>>)

Spec ==
  /\ Init
  /\ [][Next]_<<op, key, val, returnVal, store, ready>>
  /\ WF_vars(DeleteRequest, op)

THEOREM Spec => []TypeCorrectness
```