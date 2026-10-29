---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Keys, Vals, MISSING

ASSUME MISSING \notin Vals

VARIABLES op, args, ret, state, dict

vars == <<op, args, ret, state, dict>>

Ops == {"get", "insert", "update", "delete"}

NoOp == "none"

States == {"ready", "working"}

RetVals == Vals \cup {MISSING, "ok", "error"}

ArgVals == {<<>>}
           \cup {<<k>> : k \in Keys}
           \cup {<<k, v>> : k \in Keys, v \in Vals}

TypeOK ==
    /\ op \in Ops \cup {NoOp}
    /\ args \in ArgVals
    /\ ret \in RetVals
    /\ state \in States
    /\ dict \in [Keys -> Vals \cup {MISSING}]

Init ==
    /\ op = NoOp
    /\ args = <<>>
    /\ ret = MISSING
    /\ state = "ready"
    /\ dict = [k \in Keys |-> MISSING]

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

DeleteRequest == \E k \in Keys : DeleteReq(k)

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
       IN IF dict[k] # MISSING
             THEN /\ dict' = [dict EXCEPT ![k] = v]
                  /\ ret' = "ok"
             ELSE /\ ret' = "error"
                  /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

DeleteResp ==
    /\ state = "working"
    /\ op = "delete"
    /\ LET k == args[1]
       IN IF dict[k] # MISSING
             THEN /\ dict' = [dict EXCEPT ![k] = MISSING]
                  /\ ret' = "ok"
             ELSE /\ ret' = "error"
                  /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

-----------------------------------------------------------------------------

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ DeleteRequest
    \/ GetResp
    \/ InsertResp
    \/ UpdateResp
    \/ DeleteResp

Spec == Init /\ [][Next]_vars /\ WF_op(DeleteRequest)

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK

=============================================================================