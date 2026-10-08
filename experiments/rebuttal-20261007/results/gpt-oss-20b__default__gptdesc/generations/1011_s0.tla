MODULE KeyValueStore
EXTENDS TLC

CONSTANTS Keys, Vals, MISSING, NULL, GET, INSERT, UPDATE, DELETE, NONE

VARIABLES store, op, keyArg, valArg, retVal, ready, working

vars == <<store, op, keyArg, valArg, retVal, ready, working>>

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ op = NONE
  /\ keyArg = NULL
  /\ valArg = NULL
  /\ retVal = NULL
  /\ ready = TRUE
  /\ working = FALSE

TypeOK ==
  /\ store ∈ [Keys -> Vals ∪ {MISSING}]
  /\ op ∈ {GET,INSERT,UPDATE,DELETE,NONE}
  /\ keyArg ∈ Keys ∪ {NULL}
  /\ valArg ∈ Vals ∪ {NULL}
  /\ retVal ∈ Vals ∪ {MISSING} ∪ {NULL}
  /\ ready ∈ BOOLEAN
  /\ working ∈ BOOLEAN

Safety == TypeOK

GetReq ==
  /\ ready
  /\ NOT working
  /\ op' = GET
  /\ keyArg' \in Keys
  /\ valArg' = NULL
  /\ retVal' = NULL
  /\ ready' = FALSE
  /\ working' = TRUE
  /\ store' = store

InsertReq ==
  /\ ready
  /\ NOT working
  /\ op' = INSERT
  /\ keyArg' \in Keys
  /\ valArg' \in Vals
  /\ retVal' = NULL
  /\ ready' = FALSE
  /\ working' = TRUE
  /\ store' = store

UpdateReq ==
  /\ ready
  /\ NOT working
  /\ op' = UPDATE
  /\ keyArg' \in Keys
  /\ valArg' \in Vals
  /\ retVal' = NULL
  /\ ready' = FALSE
  /\ working' = TRUE
  /\ store' = store

DeleteReq ==
  /\ ready
  /\ NOT working
  /\ op' = DELETE
  /\ keyArg' \in Keys
  /\ valArg' = NULL
  /\ retVal' = NULL
  /\ ready' = FALSE
  /\ working' = TRUE
  /\ store' = store

GetResp ==
  /\ working
  /\ op = GET
  /\ keyArg ∈ Keys
  /\ retVal' = store[keyArg]
  /\ op' = NONE
  /\ keyArg' = NULL
  /\ valArg' = NULL
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ store' = store

InsertResp ==
  /\ working
  /\ op = INSERT
  /\ keyArg ∈ Keys
  /\ valArg ∈ Vals
  /\ store' = [store EXCEPT ![keyArg] = valArg]
  /\ retVal' = NULL
  /\ op' = NONE
  /\ keyArg' = NULL
  /\ valArg' = NULL
  /\ ready' = TRUE
  /\ working' = FALSE

UpdateResp ==
  /\ working
  /\ op = UPDATE
  /\ keyArg ∈ Keys
  /\ valArg ∈ Vals
  /\ store' = [store EXCEPT ![keyArg] = valArg]
  /\ retVal' = NULL
  /\ op' = NONE
  /\ keyArg' = NULL
  /\ valArg' = NULL
  /\ ready' = TRUE
  /\ working' = FALSE

DeleteResp ==
  /\ working
  /\ op = DELETE
  /\ keyArg ∈ Keys
  /\ store' = [store EXCEPT ![keyArg] = MISSING]
  /\ retVal' = NULL
  /\ op' = NONE
  /\ keyArg' = NULL
  /\ valArg' = NULL
  /\ ready' = TRUE
  /\ working' = FALSE

Stutter ==
  /\ store' = store
  /\ op' = op
  /\ keyArg' = keyArg
  /\ valArg' = valArg
  /\ retVal' = retVal
  /\ ready' = ready
  /\ working' = working

Next ==
  \/ GetReq
  \/ InsertReq
  \/ UpdateReq
  \/ DeleteReq
  \/ GetResp
  \/ InsertResp
  \/ UpdateResp
  \/ DeleteResp
  \/ Stutter

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(op = DELETE) /\ Safety

END MODULE