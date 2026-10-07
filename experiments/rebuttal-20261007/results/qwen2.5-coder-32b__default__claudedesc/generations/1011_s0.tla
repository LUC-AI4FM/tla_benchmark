------------------------------- MODULE KeyValueStore -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Keys, Vals, MISSING, NIL
ASSUME DISTINCT <<MISSING, NIL>>, Vals
ASSUME Keys \cap (Vals \cup {MISSING} \cup {NIL}) = {}

VARIABLES op, args, ret, dict, state

Init == /\ op = NIL
        /\ args = NIL
        /\ ret = NIL
        /\ dict \in [Keys -> {MISSING} \cup Vals]
        /\ state = "ready"

Next ==
    \/ /\ state = "ready"
       /\ \/ /\ op = "get"
              /\ args \in Keys
              /\ ret = dict[args]
              /\ UNCHANGED <<dict, state>>
          \/ /\ op = "insert"
              /\ args \in [Keys -> Vals]
              /\ dict[args[1]] = MISSING
              /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
              /\ ret' = "ok"
              /\ state' = "ready"
          \/ /\ op = "insert"
              /\ args \in [Keys -> Vals]
              /\ dict[args[1]] \in Vals
              /\ UNCHANGED <<dict, ret>>
              /\ state' = "ready"
          \/ /\ op = "update"
              /\ args \in [Keys -> Vals]
              /\ dict[args[1]] \in Vals
              /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
              /\ ret' = "ok"
              /\ state' = "ready"
          \/ /\ op = "update"
              /\ args \in [Keys -> Vals]
              /\ dict[args[1]] = MISSING
              /\ UNCHANGED <<dict, ret>>
              /\ state' = "ready"
          \/ /\ op = "delete"
              /\ args \in Keys
              /\ dict' = [dict EXCEPT ![args] = MISSING]
              /\ ret' = "ok"
              /\ state' = "ready"
       /\ op' = NIL
       /\ args' = NIL
    \/ /\ state = "ready"
       /\ op \in {"get", "insert", "update", "delete"}
       /\ args \in (IF op = "get" THEN Keys ELSE [Keys -> Vals])
       /\ ret' = NIL
       /\ state' = "working"

Spec == Init /\ [][Next]_<<op, args, ret, dict, state>>

TypeOK ==
    /\ op \in {"get", "insert", "update", "delete"} \cup {NIL}
    /\ (op = NIL => args = NIL)
    /\ (op \in {"get", "delete"} => args \in Keys)
    /\ (op \in {"insert", "update"} => args \in [Keys -> Vals])
    /\ ret \in Vals \cup {"ok", "error", MISSING} \cup {NIL}
    /\ dict \in [Keys -> {MISSING} \cup Vals]
    /\ state \in {"ready", "working"}

WF_delete ==
    WF_vars(<<op, args>>, UNCHANGED <<ret, dict, state>>)

=============================================================================