------------------------------ MODULE KeyValueStore ------------------------------

CONSTANTS Keys, Vals, MISSING

ASSUME MISSING ∉ Vals

VARIABLES store, op, argK, argV, ret, ready

Ops == {"none", "get", "insert", "update", "delete"}

TypeOK ==
  /\ store \in [Keys -> Vals \cup {MISSING}]
  /\ op \in Ops
  /\ argK \in Keys
  /\ argV \in Vals
  /\ ret \in Vals \cup {MISSING}
  /\ ready \in BOOLEAN

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ op = "none"
  /\ ready = TRUE
  /\ argK \in Keys
  /\ argV \in Vals
  /\ ret \in Vals \cup {MISSING}
  /\ TypeOK

GetReq ==
  /\ ready
  /\ op = "none"
  /\ op' = "get"
  /\ argK' \in Keys
  /\ ready' = FALSE
  /\ UNCHANGED <<store, argV, ret>>

GetResp ==
  /\ ~ready
  /\ op = "get"
  /\ ret' = store[argK]
  /\ op' = "none"
  /\ ready' = TRUE
  /\ UNCHANGED <<store, argK, argV>>

InsertReq ==
  /\ ready
  /\ op = "none"
  /\ op' = "insert"
  /\ argK' \in Keys
  /\ argV' \in Vals
  /\ ready' = FALSE
  /\ UNCHANGED <<store, ret>>

InsertResp ==
  /\ ~ready
  /\ op = "insert"
  /\ ret' = store[argK]
  /\ store' = [store EXCEPT ![argK] = argV]
  /\ op' = "none"
  /\ ready' = TRUE
  /\ UNCHANGED <<argK, argV>>

UpdateReq ==
  /\ ready
  /\ op = "none"
  /\ op' = "update"
  /\ argK' \in Keys
  /\ argV' \in Vals
  /\ ready' = FALSE
  /\ UNCHANGED <<store, ret>>

UpdateResp ==
  /\ ~ready
  /\ op = "update"
  /\ ret' = store[argK]
  /\ store' = [store EXCEPT ![argK] = argV]
  /\ op' = "none"
  /\ ready' = TRUE
  /\ UNCHANGED <<argK, argV>>

DeleteReq ==
  /\ ready
  /\ op = "none"
  /\ op' = "delete"
  /\ argK' \in Keys
  /\ ready' = FALSE
  /\ UNCHANGED <<store, argV, ret>>

DeleteResp ==
  /\ ~ready
  /\ op = "delete"
  /\ ret' = store[argK]
  /\ store' = [store EXCEPT ![argK] = MISSING]
  /\ op' = "none"
  /\ ready' = TRUE
  /\ UNCHANGED <<argK, argV>>

Next ==
  \/ GetReq
  \/ GetResp
  \/ InsertReq
  \/ InsertResp
  \/ UpdateReq
  \/ UpdateResp
  \/ DeleteReq
  \/ DeleteResp

vars == <<store, op, argK, argV, ret, ready>>

Spec == Init /\ [][Next]_vars /\ WF_op(DeleteReq)

===============================================================================