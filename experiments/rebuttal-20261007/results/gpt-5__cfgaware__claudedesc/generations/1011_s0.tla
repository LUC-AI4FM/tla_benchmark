------------------------------ MODULE KVStore ------------------------------

CONSTANTS Keys, Vals, MISSING, NIL

VARIABLES op, args, ret, dict, state

Ops     == {"get", "insert", "update", "delete"}
Replies == {"ok", "error"}

vars == << op, args, ret, dict, state >>

TypeOK ==
  /\ op \in Ops \cup {NIL}
  /\ args \in {NIL} \cup {<<k>> : k \in Keys} \cup (Keys \X Vals)
  /\ ret \in (Vals \cup {MISSING}) \cup Replies \cup {NIL}
  /\ dict \in [Keys -> Vals \cup {MISSING}]
  /\ state \in {"ready", "working"}

Init ==
  /\ op   = NIL
  /\ args = NIL
  /\ ret  = NIL
  /\ dict \in [Keys -> Vals \cup {MISSING}]
  /\ state = "ready"

GetReq ==
  \E k \in Keys:
    /\ state = "ready"
    /\ op = NIL
    /\ args = NIL
    /\ op'   = "get"
    /\ args' = <<k>>
    /\ state' = "working"
    /\ UNCHANGED <<dict, ret>>

InsertReq ==
  \E k \in Keys, v \in Vals:
    /\ state = "ready"
    /\ op = NIL
    /\ args = NIL
    /\ op'   = "insert"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<dict, ret>>

UpdateReq ==
  \E k \in Keys, v \in Vals:
    /\ state = "ready"
    /\ op = NIL
    /\ args = NIL
    /\ op'   = "update"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<dict, ret>>

DeleteReq ==
  \E k \in Keys:
    /\ state = "ready"
    /\ op = NIL
    /\ args = NIL
    /\ op'   = "delete"
    /\ args' = <<k>>
    /\ state' = "working"
    /\ UNCHANGED <<dict, ret>>

GetResp ==
  /\ state = "working"
  /\ op = "get"
  /\ args \in {<<k>> : k \in Keys}
  /\ ret' = dict[args[1]]
  /\ state' = "ready"
  /\ op' = NIL
  /\ args' = NIL
  /\ UNCHANGED dict

InsertResp ==
  /\ state = "working"
  /\ op = "insert"
  /\ args \in Keys \X Vals
  /\ LET k == args[1] IN
     LET v == args[2] IN
       /\ state' = "ready"
       /\ op' = NIL
       /\ args' = NIL
       /\ IF dict[k] = MISSING
            THEN /\ dict' = [dict EXCEPT ![k] = v]
                 /\ ret' = "ok"
            ELSE /\ UNCHANGED dict
                 /\ ret' = "error"

UpdateResp ==
  /\ state = "working"
  /\ op = "update"
  /\ args \in Keys \X Vals
  /\ LET k == args[1] IN
     LET v == args[2] IN
       /\ state' = "ready"
       /\ op' = NIL
       /\ args' = NIL
       /\ IF dict[k] # MISSING
            THEN /\ dict' = [dict EXCEPT ![k] = v]
                 /\ ret' = "ok"
            ELSE /\ UNCHANGED dict
                 /\ ret' = "error"

DeleteResp ==
  /\ state = "working"
  /\ op = "delete"
  /\ args \in {<<k>> : k \in Keys}
  /\ dict' = [dict EXCEPT ![args[1]] = MISSING]
  /\ ret' = "ok"
  /\ state' = "ready"
  /\ op' = NIL
  /\ args' = NIL

Next ==
  GetReq \/ InsertReq \/ UpdateReq \/ DeleteReq
  \/ GetResp \/ InsertResp \/ UpdateResp \/ DeleteResp

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(DeleteReq)

=============================================================================