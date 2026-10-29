--------------------------- MODULE KeyValueStore ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Keys, Vals, MISSING

ASSUME MISSING \notin Vals

VARIABLES op, args, ret, state, dict

vars == <<op, args, ret, state, dict>>

Ops == {"get", "insert", "update", "delete"}

States == {"ready", "working"}

RetVals == Vals \cup {MISSING, "ok", "error"}

ArgVals == [key : Keys, val : Vals \cup {MISSING}]

TypeOK ==
    /\ op \in Ops
    /\ args \in ArgVals
    /\ ret \in RetVals
    /\ state \in States
    /\ dict \in [Keys -> Vals \cup {MISSING}]

Init ==
    /\ op \in Ops
    /\ args \in ArgVals
    /\ ret = "ok"
    /\ state = "ready"
    /\ dict = [k \in Keys |-> MISSING]

-----------------------------------------------------------------------------
(* Get *)

GetReq(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = [key |-> k, val |-> MISSING]
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

GetResp ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = dict[args.key]
    /\ state' = "ready"
    /\ UNCHANGED <<op, args, dict>>

(* Insert *)

InsertReq(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = [key |-> k, val |-> v]
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

InsertResp ==
    /\ state = "working"
    /\ op = "insert"
    /\ IF dict[args.key] = MISSING
         THEN /\ dict' = [dict EXCEPT ![args.key] = args.val]
              /\ ret' = "ok"
         ELSE /\ ret' = "error"
              /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

(* Update *)

UpdateReq(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = [key |-> k, val |-> v]
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

UpdateResp ==
    /\ state = "working"
    /\ op = "update"
    /\ IF dict[args.key] # MISSING
         THEN /\ dict' = [dict EXCEPT ![args.key] = args.val]
              /\ ret' = "ok"
         ELSE /\ ret' = "error"
              /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

(* Delete *)

DeleteReq(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = [key |-> k, val |-> MISSING]
    /\ state' = "working"
    /\ UNCHANGED <<ret, dict>>

DeleteResp ==
    /\ state = "working"
    /\ op = "delete"
    /\ IF dict[args.key] # MISSING
         THEN /\ dict' = [dict EXCEPT ![args.key] = MISSING]
              /\ ret' = "ok"
         ELSE /\ ret' = "error"
              /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

-----------------------------------------------------------------------------

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ GetResp
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ InsertResp
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ UpdateResp
    \/ \E k \in Keys : DeleteReq(k)
    \/ DeleteResp

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_op(\E k \in Keys : DeleteReq(k))

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK

=============================================================================