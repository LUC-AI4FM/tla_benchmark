---------------------------- MODULE KeyValueStore ----------------------------

EXTENDS Sequences, FiniteSets, TLC

CONSTANTS Keys, Values, Missing

VARIABLES store, phase, op, args, result

vars == <<store, phase, op, args, result>>

Operations == {"get", "insert", "update", "delete", "none"}

Results == Values \cup {"ok", "error", Missing}

TypeInvariant ==
    /\ store \in [Keys -> Values \cup {Missing}]
    /\ phase \in {"idle", "processing", "done"}
    /\ op \in Operations
    /\ args \in [key: Keys \cup {Missing}, value: Values \cup {Missing}]
    /\ result \in Results \cup {Missing}

Init ==
    /\ store = [k \in Keys |-> Missing]
    /\ phase = "idle"
    /\ op = "none"
    /\ args = [key |-> Missing, value |-> Missing]
    /\ result = Missing

RequestGet(k) ==
    /\ phase = "idle"
    /\ phase' = "processing"
    /\ op' = "get"
    /\ args' = [key |-> k, value |-> Missing]
    /\ UNCHANGED <<store, result>>

RequestInsert(k, v) ==
    /\ phase = "idle"
    /\ phase' = "processing"
    /\ op' = "insert"
    /\ args' = [key |-> k, value |-> v]
    /\ UNCHANGED <<store, result>>

RequestUpdate(k, v) ==
    /\ phase = "idle"
    /\ phase' = "processing"
    /\ op' = "update"
    /\ args' = [key |-> k, value |-> v]
    /\ UNCHANGED <<store, result>>

RequestDelete(k) ==
    /\ phase = "idle"
    /\ phase' = "processing"
    /\ op' = "delete"
    /\ args' = [key |-> k, value |-> Missing]
    /\ UNCHANGED <<store, result>>

ProcessGet ==
    /\ phase = "processing"
    /\ op = "get"
    /\ result' = store[args.key]
    /\ phase' = "done"
    /\ UNCHANGED <<store, op, args>>

ProcessInsert ==
    /\ phase = "processing"
    /\ op = "insert"
    /\ IF store[args.key] = Missing
       THEN /\ store' = [store EXCEPT ![args.key] = args.value]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ phase' = "done"
    /\ UNCHANGED <<op, args>>

ProcessUpdate ==
    /\ phase = "processing"
    /\ op = "update"
    /\ IF store[args.key] # Missing
       THEN /\ store' = [store EXCEPT ![args.key] = args.value]
            /\ result' = "ok"
       ELSE /\ result' = "error"
            /\ UNCHANGED store
    /\ phase' = "done"
    /\ UNCHANGED <<op, args>>

ProcessDelete ==
    /\ phase = "processing"
    /\ op = "delete"
    /\ store' = [store EXCEPT ![args.key] = Missing]
    /\ result' = "ok"
    /\ phase' = "done"
    /\ UNCHANGED <<op, args>>

Complete ==
    /\ phase = "done"
    /\ phase' = "idle"
    /\ op' = "none"
    /\ args' = [key |-> Missing, value |-> Missing]
    /\ result' = Missing
    /\ UNCHANGED store

Request ==
    \/ \E k \in Keys : RequestGet(k)
    \/ \E k \in Keys, v \in Values : RequestInsert(k, v)
    \/ \E k \in Keys, v \in Values : RequestUpdate(k, v)
    \/ \E k \in Keys : RequestDelete(k)

Process ==
    \/ ProcessGet
    \/ ProcessInsert
    \/ ProcessUpdate
    \/ ProcessDelete

Next ==
    \/ Request
    \/ Process
    \/ Complete

DeleteFairness ==
    \A k \in Keys : WF_vars(RequestDelete(k) \/ ProcessDelete)

Spec == Init /\ [][Next]_vars /\ DeleteFairness

DeleteProgress ==
    \A k \in Keys : (phase = "processing" /\ op = "delete" /\ args.key = k) ~> (phase = "done")

=============================================================================