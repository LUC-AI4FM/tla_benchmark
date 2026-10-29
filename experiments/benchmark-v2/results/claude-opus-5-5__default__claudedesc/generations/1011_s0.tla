--------------------------- MODULE KeyValueStore ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Keys, Vals, MISSING, NIL

Ops == {"get", "insert", "update", "delete"}

ASSUME /\ MISSING \notin Vals
       /\ NIL \notin Vals
       /\ MISSING # NIL
       /\ MISSING \notin Ops
       /\ NIL \notin Ops
       /\ MISSING \notin {"ok", "error"}
       /\ NIL \notin {"ok", "error"}

VARIABLES op, args, ret, dict, state

vars == <<op, args, ret, dict, state>>

TypeOK ==
    /\ op \in Ops \cup {NIL}
    /\ args \in {NIL} \cup {<<k>> : k \in Keys} \cup (Keys \X Vals)
    /\ ret \in Vals \cup {"ok", "error", MISSING, NIL}
    /\ dict \in [Keys -> Vals \cup {MISSING}]
    /\ state \in {"ready", "working"}

Init ==
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ dict = [k \in Keys |-> MISSING]
    /\ state = "ready"

-----------------------------------------------------------------------------
(* Requests *)

GetReq(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<k>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

InsertReq(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

UpdateReq(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

DeleteReq(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = <<k>>
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

-----------------------------------------------------------------------------
(* Responses *)

GetResp ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = dict[args[1]]
    /\ state' = "ready"
    /\ UNCHANGED <<op, args, dict>>

InsertResp ==
    /\ state = "working"
    /\ op = "insert"
    /\ LET k == args[1]
           v == args[2]
       IN IF dict[k] = MISSING
             THEN /\ dict' = [dict EXCEPT ![k] = v]
                  /\ ret' = "ok"
             ELSE /\ ret' = "error"
                  /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

UpdateResp ==
    /\ state = "working"
    /\ op = "update"
    /\ LET k == args[1]
           v == args[2]
       IN IF dict[k] = MISSING
             THEN /\ ret' = "error"
                  /\ UNCHANGED dict
             ELSE /\ dict' = [dict EXCEPT ![k] = v]
                  /\ ret' = "ok"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

DeleteResp ==
    /\ state = "working"
    /\ op = "delete"
    /\ dict' = [dict EXCEPT ![args[1]] = MISSING]
    /\ ret' = "ok"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

-----------------------------------------------------------------------------

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ \E k \in Keys : DeleteReq(k)
    \/ GetResp
    \/ InsertResp
    \/ UpdateResp
    \/ DeleteResp

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(\E k \in Keys : DeleteReq(k))

THEOREM Spec => []TypeOK

=============================================================================