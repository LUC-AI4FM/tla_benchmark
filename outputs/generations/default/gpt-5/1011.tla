---------------------------- MODULE KeyValueStore ----------------------------

EXTENDS TLC

CONSTANTS
  Keys, Vals, MISSING, Null

ASSUME MISSING \notin Vals

VARIABLES store, ready, working, op, k, v, ret

Ops == {"get", "insert", "update", "delete"}
Ret == Vals \cup {MISSING} \cup {"OK", "ERROR"}
ValsOrMissing == Vals \cup {MISSING}
Vars == << store, ready, working, op, k, v, ret >>

TypeOK ==
  /\ store \in [Keys -> ValsOrMissing]
  /\ ready \in BOOLEAN
  /\ working \in BOOLEAN
  /\ op \in Ops \cup {Null}
  /\ k \in Keys \cup {Null}
  /\ v \in Vals \cup {Null}
  /\ ret \in (Ret \cup {Null})

Inv ==
  /\ TypeOK
  /\ ready = ~working
  /\ working => op \in Ops
  /\ ready => op = Null
  /\ working => ret = Null

Init ==
  /\ store = [kk \in Keys |-> MISSING]
  /\ ready = TRUE
  /\ working = FALSE
  /\ op = Null
  /\ k = Null
  /\ v = Null
  /\ ret = Null

GetReq ==
  /\ ready
  /\ ~working
  /\ op = Null
  /\ \E kk \in Keys:
       /\ store' = store
       /\ ready' = FALSE
       /\ working' = TRUE
       /\ op' = "get"
       /\ k' = kk
       /\ v' = Null
       /\ ret' = Null

GetResp ==
  /\ working
  /\ op = "get"
  /\ store' = store
  /\ ret' = store[k]
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ op' = Null
  /\ k' = Null
  /\ v' = Null

InsertReq ==
  /\ ready
  /\ ~working
  /\ op = Null
  /\ \E kk \in Keys, vv \in Vals:
       /\ store' = store
       /\ ready' = FALSE
       /\ working' = TRUE
       /\ op' = "insert"
       /\ k' = kk
       /\ v' = vv
       /\ ret' = Null

InsertResp ==
  /\ working
  /\ op = "insert"
  /\ IF store[k] = MISSING
     THEN /\ store' = [store EXCEPT ![k] = v]
          /\ ret' = "OK"
     ELSE /\ store' = store
          /\ ret' = "ERROR"
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ op' = Null
  /\ k' = Null
  /\ v' = Null

UpdateReq ==
  /\ ready
  /\ ~working
  /\ op = Null
  /\ \E kk \in Keys, vv \in Vals:
       /\ store' = store
       /\ ready' = FALSE
       /\ working' = TRUE
       /\ op' = "update"
       /\ k' = kk
       /\ v' = vv
       /\ ret' = Null

UpdateResp ==
  /\ working
  /\ op = "update"
  /\ IF store[k] # MISSING
     THEN /\ store' = [store EXCEPT ![k] = v]
          /\ ret' = "OK"
     ELSE /\ store' = store
          /\ ret' = "ERROR"
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ op' = Null
  /\ k' = Null
  /\ v' = Null

DeleteReq ==
  /\ ready
  /\ ~working
  /\ op = Null
  /\ \E kk \in Keys:
       /\ store' = store
       /\ ready' = FALSE
       /\ working' = TRUE
       /\ op' = "delete"
       /\ k' = kk
       /\ v' = Null
       /\ ret' = Null

DeleteResp ==
  /\ working
  /\ op = "delete"
  /\ IF store[k] # MISSING
     THEN /\ store' = [store EXCEPT ![k] = MISSING]
          /\ ret' = "OK"
     ELSE /\ store' = store
          /\ ret' = "ERROR"
  /\ ready' = TRUE
  /\ working' = FALSE
  /\ op' = Null
  /\ k' = Null
  /\ v' = Null

Next ==
  \/ GetReq
  \/ GetResp
  \/ InsertReq
  \/ InsertResp
  \/ UpdateReq
  \/ UpdateResp
  \/ DeleteReq
  \/ DeleteResp

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(DeleteReq)

Safety == []Inv
Liveness == WF_Vars(DeleteReq)

=============================================================================