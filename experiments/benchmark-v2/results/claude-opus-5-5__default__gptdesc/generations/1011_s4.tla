---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Keys, Vals, MISSING

ASSUME MISSING \notin Vals

VARIABLES op, args, ret, state, dict

vars == <<op, args, ret, state, dict>>

Ops == {"get", "insert", "update", "delete"}

NoOp == "none"
Ok   == "ok"
Err  == "error"
NoRet == "noret"

ArgSet == {<<>>}
          \cup {<<k>> : k \in Keys}
          \cup {<<k, v>> : k \in Keys, v \in Vals}

RetSet == Vals \cup {MISSING, Ok, Err, NoRet}

TypeOK ==
    /\ op \in Ops \cup {NoOp}
    /\ args \in ArgSet
    /\ ret \in RetSet
    /\ state \in {"ready", "working"}
    /\ dict \in [Keys -> Vals \cup {MISSING}]

Init ==
    /\ op = NoOp
    /\ args = <<>>
    /\ ret = NoRet
    /\ state = "ready"
    /\ dict = [k \in Keys |-> MISSING]

-----------------------------------------------------------------------------
(* Requests *)

GetReq(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<k>>
    /\ ret' = NoRet
    /\ state' = "working"
    /\ UNCHANGED dict

InsertReq(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ ret' = NoRet
    /\ state' = "working"
    /\ UNCHANGED dict

UpdateReq(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ ret' = NoRet
    /\ state' = "working"
    /\ UNCHANGED dict

DeleteReq(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = <<k>>
    /\ ret' = NoRet
    /\ state' = "working"
    /\ UNCHANGED dict

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
               /\ ret' = Ok
          ELSE /\ UNCHANGED dict
               /\ ret' = Err
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

UpdateResp ==
    /\ state = "working"
    /\ op = "update"
    /\ LET k == args[1]
           v == args[2]
       IN IF dict[k] # MISSING
          THEN /\ dict' = [dict EXCEPT ![k] = v]
               /\ ret' = Ok
          ELSE /\ UNCHANGED dict
               /\ ret' = Err
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

DeleteResp ==
    /\ state = "working"
    /\ op = "delete"
    /\ LET k == args[1]
       IN IF dict[k] # MISSING
          THEN /\ dict' = [dict EXCEPT ![k] = MISSING]
               /\ ret' = Ok
          ELSE /\ UNCHANGED dict
               /\ ret' = Err
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

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_op(\E k \in Keys : DeleteReq(k))

THEOREM Spec => []TypeOK
=============================================================================