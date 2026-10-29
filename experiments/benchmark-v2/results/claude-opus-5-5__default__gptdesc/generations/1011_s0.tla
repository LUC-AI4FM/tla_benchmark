---------------------------- MODULE KeyValueStore ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Keys,      \* The set of keys
          Vals,      \* The set of values
          MISSING    \* Distinguished marker for an absent value

ASSUME MISSING \notin Vals

VARIABLES dict,   \* The store: Keys -> Vals \cup {MISSING}
          op,     \* Current operation
          args,   \* Arguments of the current operation
          ret,    \* Return value of the current operation
          state   \* "ready" or "working"

vars == <<dict, op, args, ret, state>>

Ops     == {"get", "insert", "update", "delete"}
NoOp    == "none"
States  == {"ready", "working"}
RetVals == Vals \cup {MISSING, "ok", "error", "none"}

Args == {<<k>> : k \in Keys} \cup {<<k, v>> : k \in Keys, v \in Vals} \cup {<<>>}

TypeOK ==
    /\ dict \in [Keys -> Vals \cup {MISSING}]
    /\ op \in Ops \cup {NoOp}
    /\ args \in Args
    /\ ret \in RetVals
    /\ state \in States

Init ==
    /\ dict = [k \in Keys |-> MISSING]
    /\ op = NoOp
    /\ args = <<>>
    /\ ret = "none"
    /\ state = "ready"

-----------------------------------------------------------------------------
(* Requests *)

GetReq(k) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<k>>
    /\ ret' = "none"
    /\ state' = "working"
    /\ UNCHANGED dict

InsertReq(k, v) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ ret' = "none"
    /\ state' = "working"
    /\ UNCHANGED dict

UpdateReq(k, v) ==
    /\ state = "ready"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ ret' = "none"
    /\ state' = "working"
    /\ UNCHANGED dict

DeleteReq(k) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = <<k>>
    /\ ret' = "none"
    /\ state' = "working"
    /\ UNCHANGED dict

(* Responses *)

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

AnyDeleteReq == \E k \in Keys : DeleteReq(k)

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ AnyDeleteReq
    \/ GetResp
    \/ InsertResp
    \/ UpdateResp
    \/ DeleteResp

Spec == Init /\ [][Next]_vars /\ WF_op(AnyDeleteReq)

-----------------------------------------------------------------------------
(* Properties *)

THEOREM Spec => []TypeOK

=============================================================================