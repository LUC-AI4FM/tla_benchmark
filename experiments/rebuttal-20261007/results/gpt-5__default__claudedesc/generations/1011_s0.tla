--------------------------- MODULE KeyValueStore ---------------------------

EXTENDS Naturals, Sequences

CONSTANTS Keys, Vals, MISSING, NIL

(*
  Assumptions about sentinels being distinct from values and operation names.
*)
ASSUME
  /\ MISSING # NIL
  /\ MISSING \notin Vals
  /\ NIL \notin Vals
  /\ MISSING \notin {"get","insert","update","delete"}
  /\ NIL \notin {"get","insert","update","delete"}

(*
  State variables
*)
VARIABLES op, args, ret, dict, state

vars == << op, args, ret, dict, state >>

Ops     == {"get","insert","update","delete"}
RetSyms == {"ok","error"}
States  == {"ready","working"}
Pairs   == { <<k, v>> : k \in Keys, v \in Vals }

(*
  Typing invariant
*)
TypeOK ==
  /\ op \in Ops \cup {NIL}
  /\ args \in {NIL} \cup Keys \cup Pairs
  /\ ret \in Vals \cup {MISSING, "ok", "error", NIL}
  /\ dict \in [Keys -> Vals \cup {MISSING}]
  /\ state \in States

(*
  Initial state: ready, no pending op, arbitrary store of correct type
*)
Init ==
  /\ op = NIL
  /\ args = NIL
  /\ ret = NIL
  /\ state = "ready"
  /\ dict \in [Keys -> Vals \cup {MISSING}]

(*
  Request actions: move from ready to working and set op/args
*)
GetReq(k) ==
  /\ state = "ready"
  /\ op = NIL
  /\ k \in Keys
  /\ op' = "get"
  /\ args' = k
  /\ state' = "working"
  /\ UNCHANGED <<ret, dict>>

InsertReq(k, v) ==
  /\ state = "ready"
  /\ op = NIL
  /\ k \in Keys
  /\ v \in Vals
  /\ op' = "insert"
  /\ args' = <<k, v>>
  /\ state' = "working"
  /\ UNCHANGED <<ret, dict>>

UpdateReq(k, v) ==
  /\ state = "ready"
  /\ op = NIL
  /\ k \in Keys
  /\ v \in Vals
  /\ op' = "update"
  /\ args' = <<k, v>>
  /\ state' = "working"
  /\ UNCHANGED <<ret, dict>>

DeleteReq(k) ==
  /\ state = "ready"
  /\ op = NIL
  /\ k \in Keys
  /\ op' = "delete"
  /\ args' = k
  /\ state' = "working"
  /\ UNCHANGED <<ret, dict>>

(*
  Response actions: perform the operation and return to ready
*)
GetResp ==
  /\ state = "working"
  /\ op = "get"
  /\ args \in Keys
  /\ ret' = dict[args]
  /\ dict' = dict
  /\ op' = NIL
  /\ args' = NIL
  /\ state' = "ready"

InsertResp ==
  /\ state = "working"
  /\ op = "insert"
  /\ args \in Pairs
  /\ LET k == args[1]
         v == args[2]
     IN IF dict[k] = MISSING
           THEN /\ dict' = [dict EXCEPT ![k] = v]
                /\ ret' = "ok"
           ELSE /\ dict' = dict
                /\ ret' = "error"
  /\ op' = NIL
  /\ args' = NIL
  /\ state' = "ready"

UpdateResp ==
  /\ state = "working"
  /\ op = "update"
  /\ args \in Pairs
  /\ LET k == args[1]
         v == args[2]
     IN IF dict[k] # MISSING
           THEN /\ dict' = [dict EXCEPT ![k] = v]
                /\ ret' = "ok"
           ELSE /\ dict' = dict
                /\ ret' = "error"
  /\ op' = NIL
  /\ args' = NIL
  /\ state' = "ready"

DeleteResp ==
  /\ state = "working"
  /\ op = "delete"
  /\ args \in Keys
  /\ LET k == args
     IN /\ dict' = [dict EXCEPT ![k] = MISSING]
        /\ ret' = "ok"
  /\ op' = NIL
  /\ args' = NIL
  /\ state' = "ready"

Request ==
  \E k \in Keys:
      GetReq(k)
    \/ DeleteReq(k)
    \/ (\E v \in Vals: InsertReq(k, v) \/ UpdateReq(k, v))

Response ==
  GetResp \/ InsertResp \/ UpdateResp \/ DeleteResp

Next == Request \/ Response

(*
  Weak fairness for delete requests: they cannot be indefinitely postponed.
*)
DelReq == \E k \in Keys: DeleteReq(k)

Spec == Init /\ [][Next]_vars /\ WF_vars(DelReq)

(*
  Sole checked safety property (typing)
*)
THEOREM Spec => []TypeOK

============================================================================