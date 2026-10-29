------------------------------ MODULE KVStore ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Keys, Vals

ASSUME Keys # {} /\ Vals # {}

MISSING == CHOOSE v : v \notin Vals

NONE == CHOOSE n : n \notin Keys \cup Vals \cup {MISSING}

Ops == {"get", "insert", "update", "delete"}

States == {"ready", "working"}

RetVals == Vals \cup {MISSING, "ok", "error", NONE}

VARIABLES dict, op, args, ret, state

vars == <<dict, op, args, ret, state>>

TypeOK ==
    /\ dict \in [Keys -> Vals \cup {MISSING}]
    /\ op \in Ops \cup {NONE}
    /\ args \in [key : Keys \cup {NONE}, val : Vals \cup {NONE}]
    /\ ret \in RetVals
    /\ state \in States

Init ==
    /\ dict = [k \in Keys |-> MISSING]
    /\ op = NONE
    /\ args = [key |-> NONE, val |-> NONE]
    /\ ret = NONE
    /\ state = "ready"

(***************************************************************************)
(* Requests                                                                *)
(***************************************************************************)

GetReq(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = [key |-> k, val |-> NONE]
    /\ ret' = NONE
    /\ state' = "working"
    /\ UNCHANGED dict

InsertReq(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = [key |-> k, val |-> v]
    /\ ret' = NONE
    /\ state' = "working"
    /\ UNCHANGED dict

UpdateReq(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = [key |-> k, val |-> v]
    /\ ret' = NONE
    /\ state' = "working"
    /\ UNCHANGED dict

DeleteReq(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = [key |-> k, val |-> NONE]
    /\ ret' = NONE
    /\ state' = "working"
    /\ UNCHANGED dict

(***************************************************************************)
(* Responses                                                               *)
(***************************************************************************)

GetResp ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = dict[args.key]
    /\ state' = "ready"
    /\ UNCHANGED <<dict, op, args>>

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
    /\ \A k \in Keys : WF_op(DeleteReq(k))

THEOREM Spec => []TypeOK

=============================================================================