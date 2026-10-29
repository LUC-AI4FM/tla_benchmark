---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Keys, Vals, NIL, MISSING

VARIABLES dict, op, args, ret, state

vars == <<dict, op, args, ret, state>>

Ops == {"get", "insert", "update", "delete"}

States == {"ready", "working"}

Rets == Vals \cup {MISSING, NIL, "ok", "error"}

Args == (Keys \X (Vals \cup {NIL})) \cup {<<NIL, NIL>>}

TypeOK ==
    /\ dict \in [Keys -> Vals \cup {MISSING}]
    /\ op \in Ops \cup {NIL}
    /\ args \in Args
    /\ ret \in Rets
    /\ state \in States

Init ==
    /\ dict = [k \in Keys |-> MISSING]
    /\ op = NIL
    /\ args = <<NIL, NIL>>
    /\ ret = NIL
    /\ state = "ready"

(* ---------------------------- Requests ---------------------------------- *)

GetReq(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<k, NIL>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED dict

InsertReq(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED dict

UpdateReq(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED dict

DeleteReq(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = <<k, NIL>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED dict

(* ---------------------------- Responses --------------------------------- *)

GetResp ==
    /\ state = "working"
    /\ op = "get"
    /\ ret' = dict[args[1]]
    /\ state' = "ready"
    /\ UNCHANGED <<dict, op, args>>

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
       IN IF dict[k] /= MISSING
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
       IN IF dict[k] /= MISSING
          THEN /\ dict' = [dict EXCEPT ![k] = MISSING]
               /\ ret' = "ok"
          ELSE /\ ret' = "error"
               /\ UNCHANGED dict
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

(* ---------------------------- Spec -------------------------------------- *)

DeleteRequest == \E k \in Keys : DeleteReq(k)

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

=============================================================================