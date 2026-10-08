```tla
MODULE KeyValueStore

EXTENDS Integers, TLC

CONSTANTS Vals, Keys
VARIABLES store, op, key, val, retval, ready

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ op = "none"
  /\ key = NULL
  /\ val = NULL
  /\ retval = NULL
  /\ ready = TRUE

TypeOK ==
  /\ store \in [Keys -> Vals \cup {MISSING}]
  /\ op \in {"get", "insert", "update", "delete", "none"}
  /\ key \in Keys \cup {NULL}
  /\ val \in Vals \cup {NULL}
  /\ retval \in Vals \cup {MISSING, NULL}

GetRequest ==
  /\ op = "none"
  /\ ready = TRUE
  /\ op' = "get"
  /\ key' \in Keys
  /\ val' = NULL
  /\ retval' = NULL
  /\ ready' = FALSE
  /\ store' = store

GetResponse ==
  /\ op = "get"
  /\ ready = FALSE
  /\ op' = "none"
  /\ key' = NULL
  /\ val' = NULL
  /\ retval' = IF store[key] = MISSING THEN MISSING ELSE store[key]
  /\ ready' = TRUE
  /\ store' = store

InsertRequest ==
  /\ op = "none"
  /\ ready = TRUE
  /\ op' = "insert"
  /\ key' \in Keys
  /\ val' \in Vals
  /\ retval' = NULL
  /\ ready' = FALSE
  /\ store' = store

InsertResponse ==
  /\ op = "insert"
  /\ ready = FALSE
  /\ op' = "none"
  /\ key' = NULL
  /\ val' = NULL
  /\ retval' = MISSING
  /\ ready' = TRUE
  /\ store' = [store EXCEPT ![key] = val]

UpdateRequest ==
  /\ op = "none"
  /\ ready = TRUE
  /\ op' = "update"
  /\ key' \in Keys
  /\ val' \in Vals
  /\ retval' = NULL
  /\ ready' = FALSE
  /\ store' = store

UpdateResponse ==
  /\ op = "update"
  /\ ready = FALSE
  /\ op' = "none"
  /\ key' = NULL
  /\ val' = NULL
  /\ retval' = IF store[key] = MISSING THEN MISSING ELSE store[key]
  /\ ready' = TRUE
  /\ store' = [store EXCEPT ![key] = val]

DeleteRequest ==
  /\ op = "none"
  /\ ready = TRUE
  /\ op' = "delete"
  /\ key' \in Keys
  /\ val' = NULL
  /\ retval' = NULL
  /\ ready' = FALSE
  /\ store' = store

DeleteResponse ==
  /\ op = "delete"
  /\ ready = FALSE
  /\ op' = "none"
  /\ key' = NULL
  /\ val' = NULL
  /\ retval' = MISSING
  /\ ready' = TRUE
  /\ store' = [store EXCEPT ![key] = MISSING]

Next ==
  \/ GetRequest
  \/ GetResponse
  \/ InsertRequest
  \/ InsertResponse
  \/ UpdateRequest
  \/ UpdateResponse
  \/ DeleteRequest
  \/ DeleteResponse
  \/ (op' = op) ∧ (key' = key) ∧ (val' = val) ∧ (retval' = retval) ∧ (ready' = ready) ∧ (store' = store)

Spec ==
  Init ∧ [][Next]_<<store, op, key, val, retval, ready>>
  ∧ WF_<<op>>(DeleteRequest)

THEOREM Spec => []TypeOK
```