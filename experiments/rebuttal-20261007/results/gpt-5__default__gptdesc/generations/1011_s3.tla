------------------------------ MODULE KeyValueStore ------------------------------

CONSTANTS Keys, Vals, MISSING, UNDEF

ASSUME /\ MISSING \notin Vals
       /\ UNDEF \notin Vals
       /\ MISSING # UNDEF

VARIABLES store, status, op, argK, argV, rv

Ops == {"get", "insert", "update", "delete"}
OpsPlusNone == Ops \cup {"none"}
Statuses == {"ready", "working"}
ValsOrMissing == Vals \cup {MISSING}
RVs == Vals \cup {MISSING} \cup BOOLEAN \cup {UNDEF}

TypeOK ==
  /\ store \in [Keys -> ValsOrMissing]
  /\ status \in Statuses
  /\ op \in OpsPlusNone
  /\ argK \in Keys \cup {UNDEF}
  /\ argV \in Vals \cup {UNDEF}
  /\ rv \in RVs

StatusOpConsistent ==
  /\ (status = "ready") => (op = "none" /\ argK = UNDEF /\ argV = UNDEF)
  /\ (status = "working") => (op \in Ops)

ArgsOK ==
  /\ (status = "working") =>
       /\ argK \in Keys
       /\ (op \in {"insert", "update"} => argV \in Vals)
       /\ (op \in {"get", "delete"} => argV = UNDEF)

SafetyInvariants == TypeOK /\ StatusOpConsistent /\ ArgsOK

Init ==
  /\ store \in [Keys -> ValsOrMissing]
  /\ status = "ready"
  /\ op = "none"
  /\ argK = UNDEF
  /\ argV = UNDEF
  /\ rv = UNDEF

GetReq ==
  /\ status = "ready"
  /\ op = "none"
  /\ \E k \in Keys:
       /\ status' = "working"
       /\ op' = "get"
       /\ argK' = k
       /\ argV' = UNDEF
       /\ rv' = UNDEF
       /\ UNCHANGED store

InsertReq ==
  /\ status = "ready"
  /\ op = "none"
  /\ \E k \in Keys:
     \E v \in Vals:
       /\ status' = "working"
       /\ op' = "insert"
       /\ argK' = k
       /\ argV' = v
       /\ rv' = UNDEF
       /\ UNCHANGED store

UpdateReq ==
  /\ status = "ready"
  /\ op = "none"
  /\ \E k \in Keys:
     \E v \in Vals:
       /\ status' = "working"
       /\ op' = "update"
       /\ argK' = k
       /\ argV' = v
       /\ rv' = UNDEF
       /\ UNCHANGED store

DeleteReq ==
  /\ status = "ready"
  /\ op = "none"
  /\ \E k \in Keys:
       /\ status' = "working"
       /\ op' = "delete"
       /\ argK' = k
       /\ argV' = UNDEF
       /\ rv' = UNDEF
       /\ UNCHANGED store

GetResp ==
  /\ status = "working"
  /\ op = "get"
  /\ status' = "ready"
  /\ op' = "none"
  /\ rv' = store[argK]
  /\ argK' = UNDEF
  /\ argV' = UNDEF
  /\ UNCHANGED store

InsertResp ==
  /\ status = "working"
  /\ op = "insert"
  /\ LET wasMissing == store[argK] = MISSING IN
       /\ store' = [store EXCEPT ![argK] = IF wasMissing THEN argV ELSE @]
       /\ rv' = wasMissing
  /\ status' = "ready"
  /\ op' = "none"
  /\ argK' = UNDEF
  /\ argV' = UNDEF

UpdateResp ==
  /\ status = "working"
  /\ op = "update"
  /\ LET canUpdate == store[argK] # MISSING IN
       /\ store' = [store EXCEPT ![argK] = IF canUpdate THEN argV ELSE @]
       /\ rv' = canUpdate
  /\ status' = "ready"
  /\ op' = "none"
  /\ argK' = UNDEF
  /\ argV' = UNDEF

DeleteResp ==
  /\ status = "working"
  /\ op = "delete"
  /\ LET existed == store[argK] # MISSING IN
       /\ store' = [store EXCEPT ![argK] = MISSING]
       /\ rv' = existed
  /\ status' = "ready"
  /\ op' = "none"
  /\ argK' = UNDEF
  /\ argV' = UNDEF

Next ==
  \/ GetReq
  \/ InsertReq
  \/ UpdateReq
  \/ DeleteReq
  \/ GetResp
  \/ InsertResp
  \/ UpdateResp
  \/ DeleteResp

vars == << store, status, op, argK, argV, rv >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_op(DeleteReq)

=============================================================================