---- MODULE KeyValueStore ----
EXTENDS TLC

CONSTANTS Keys, Vals, MISSING, NULL, OK

ASSUME
  /\ MISSING \notin Vals
  /\ NULL \notin Keys /\ NULL \notin Vals
  /\ OK \notin (Vals \cup {MISSING})

Ops == {"get", "insert", "update", "delete"}
RetVals == Vals \cup {MISSING} \cup {OK}

VARIABLES store, status, op, argK, argV, ret

vars == << store, status, op, argK, argV, ret >>

TypeOK ==
  /\ store \in [Keys -> Vals \cup {MISSING}]
  /\ status \in {"ready", "working"}
  /\ op \in Ops \cup {"none"}
  /\ argK \in Keys \cup {NULL}
  /\ argV \in Vals \cup {NULL}
  /\ ret \in (RetVals \cup {NULL})
  /\ (status = "ready") => op = "none"
  /\ (status = "working") => op \in Ops

Init ==
  /\ store = [k \in Keys |-> MISSING]
  /\ status = "ready"
  /\ op = "none"
  /\ argK = NULL
  /\ argV = NULL
  /\ ret = NULL
  /\ TypeOK

GetReq ==
  /\ status = "ready" /\ op = "none"
  /\ \E k \in Keys:
       /\ op' = "get"
       /\ argK' = k
       /\ argV' = NULL
       /\ ret' = NULL
       /\ status' = "working"
       /\ UNCHANGED store

GetResp ==
  /\ status = "working" /\ op = "get"
  /\ ret' = store[argK]
  /\ status' = "ready"
  /\ op' = "none"
  /\ argK' = NULL
  /\ argV' = NULL
  /\ UNCHANGED store

InsReq ==
  /\ status = "ready" /\ op = "none"
  /\ \E k \in Keys, v \in Vals:
       /\ op' = "insert"
       /\ argK' = k
       /\ argV' = v
       /\ ret' = NULL
       /\ status' = "working"
       /\ UNCHANGED store

InsResp ==
  /\ status = "working" /\ op = "insert"
  /\ store' = [store EXCEPT ![argK] = argV]
  /\ ret' = OK
  /\ status' = "ready"
  /\ op' = "none"
  /\ argK' = NULL
  /\ argV' = NULL

UpdReq ==
  /\ status = "ready" /\ op = "none"
  /\ \E k \in Keys, v \in Vals:
       /\ op' = "update"
       /\ argK' = k
       /\ argV' = v
       /\ ret' = NULL
       /\ status' = "working"
       /\ UNCHANGED store

UpdResp ==
  /\ status = "working" /\ op = "update"
  /\ store' = [store EXCEPT ![argK] = argV]
  /\ ret' = OK
  /\ status' = "ready"
  /\ op' = "none"
  /\ argK' = NULL
  /\ argV' = NULL

DelReq ==
  /\ status = "ready" /\ op = "none"
  /\ \E k \in Keys:
       /\ op' = "delete"
       /\ argK' = k
       /\ argV' = NULL
       /\ ret' = NULL
       /\ status' = "working"
       /\ UNCHANGED store

DelResp ==
  /\ status = "working" /\ op = "delete"
  /\ store' = [store EXCEPT ![argK] = MISSING]
  /\ ret' = OK
  /\ status' = "ready"
  /\ op' = "none"
  /\ argK' = NULL
  /\ argV' = NULL

Next ==
  GetReq \/ GetResp \/
  InsReq \/ InsResp \/
  UpdReq \/ UpdResp \/
  DelReq \/ DelResp

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_op(DelReq)

THEOREM Spec => []TypeOK

====