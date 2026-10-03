---- MODULE KeyValueStore ----
EXTENDS TLC, Sequences, FiniteSets, Strings, Integers

CONSTANTS Keys, Vals, MISSING

ASSUME  /\ IsFiniteSet(Keys)
        /\ IsFiniteSet(Vals)
        /\ Keys \subseteq STRING
        /\ Vals \subseteq INT
        /\ MISSING \notin (Vals \cup Keys \cup STRING \cup INT)

VARIABLES store, state, op, args, ret

vars == <<store, state, op, args, ret>>

OpSet == {"get", "insert", "update", "delete"}
RetValSet == Vals \cup {MISSING, "ok", "err"}

TypeOK ==
    /\ store \in [Keys -> (Vals \cup {MISSING})]
    /\ state \in {"ready", "working"}
    /\ op \in OpSet \cup {"noop"}
    /\ \/ (op = "noop" /\ args = <<>>)
       \/ (op \in {"get", "delete"} /\ Len(args) = 1 /\ args[1] \in Keys)
       \/ (op \in {"insert", "update"} /\ Len(args) = 2 /\ args[1] \in Keys /\ args[2] \in Vals)
    /\ ret \in RetValSet \cup {"none"}

Init ==
    /\ store = [k \in Keys |-> MISSING]
    /\ state = "ready"
    /\ op = "noop"
    /\ args = <<>>
    /\ ret = "none"

(* Environment actions to issue requests *)

ReqGet(k) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "get"
    /\ args' = <<k>>
    /\ UNCHANGED <<store, ret>>

ReqInsert(k, v) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ UNCHANGED <<store, ret>>

ReqUpdate(k, v) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ UNCHANGED <<store, ret>>

ReqDelete(k) ==
    /\ state = "ready"
    /\ state' = "working"
    /\ op' = "delete"
    /\ args' = <<k>>
    /\ UNCHANGED <<store, ret>>

(* System actions to process requests and respond *)

RspGet ==
    /\ state = "working"
    /\ op = "get"
    /\ LET k == args[1] IN
        ret' = store[k]
    /\ state' = "ready"
    /\ UNCHANGED <<store, op, args>>

RspInsert ==
    /\ state = "working"
    /\ op = "insert"
    /\ LET k == args[1]
           v == args[2]
       IN
       /\ IF store[k] = MISSING
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ ret' = "ok"
          ELSE /\ store' = store
               /\ ret' = "err"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

RspUpdate ==
    /\ state = "working"
    /\ op = "update"
    /\ LET k == args[1]
           v == args[2]
       IN
       /\ IF store[k] # MISSING
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ ret' = "ok"
          ELSE /\ store' = store
               /\ ret' = "err"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

RspDelete ==
    /\ state = "working"
    /\ op = "delete"
    /\ LET k == args[1] IN
       /\ IF store[k] # MISSING
          THEN /\ store' = [store EXCEPT ![k] = MISSING]
               /\ ret' = "ok"
          ELSE /\ store' = store
               /\ ret' = "err"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args>>

Next ==
    \/ \E k \in Keys : ReqGet(k)
    \/ \E k \in Keys, v \in Vals : ReqInsert(k, v)
    \/ \E k \in Keys, v \in Vals : ReqUpdate(k, v)
    \/ \E k \in Keys : ReqDelete(k)
    \/ RspGet
    \/ RspInsert
    \/ RspUpdate
    \/ RspDelete

AnyReqDelete == \E k \in Keys: ReqDelete(k)

Spec == Init /\ [][Next]_vars /\ WF_vars(AnyReqDelete)

=============================================================================