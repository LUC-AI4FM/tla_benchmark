-------------------------------- MODULE spec --------------------------------

EXTENDS Sequences, FiniteSets

CONSTANTS Keys, Values, MissingValue

VARIABLES store, op, args, result, phase

vars == <<store, op, args, result, phase>>

Operations == {"get", "insert", "update", "delete", "none"}
Results == Values \cup {"ok", "error", "missing", "none"}
Phases == {"idle", "processing", "done"}

TypeInvariant ==
    /\ store \in [Keys -> Values \cup {MissingValue}]
    /\ op \in Operations
    /\ args \in (Keys \times Values) \cup (Keys \times {MissingValue}) \cup {<<>>}
    /\ result \in Results
    /\ phase \in Phases

Init ==
    /\ store = [k \in Keys |-> MissingValue]
    /\ op = "none"
    /\ args = <<>>
    /\ result = "none"
    /\ phase = "idle"

RequestGet(k) ==
    /\ phase = "idle"
    /\ op' = "get"
    /\ args' = <<k, MissingValue>>
    /\ result' = "none"
    /\ phase' = "processing"
    /\ UNCHANGED store

RequestInsert(k, v) ==
    /\ phase = "idle"
    /\ v \in Values
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ result' = "none"
    /\ phase' = "processing"
    /\ UNCHANGED store

RequestUpdate(k, v) ==
    /\ phase = "idle"
    /\ v \in Values
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ result' = "none"
    /\ phase' = "processing"
    /\ UNCHANGED store

RequestDelete(k) ==
    /\ phase = "idle"
    /\ op' = "delete"
    /\ args' = <<k, MissingValue>>
    /\ result' = "none"
    /\ phase' = "processing"
    /\ UNCHANGED store

ProcessGet ==
    /\ phase = "processing"
    /\ op = "get"
    /\ LET k == args[1]
       IN IF store[k] = MissingValue
          THEN result' = "missing"
          ELSE result' = store[k]
    /\ phase' = "done"
    /\ UNCHANGED <<store, op, args>>

ProcessInsert ==
    /\ phase = "processing"
    /\ op = "insert"
    /\ LET k == args[1]
           v == args[2]
       IN IF store[k] = MissingValue
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ result' = "ok"
          ELSE /\ result' = "error"
               /\ UNCHANGED store
    /\ phase' = "done"
    /\ UNCHANGED <<op, args>>

ProcessUpdate ==
    /\ phase = "processing"
    /\ op = "update"
    /\ LET k == args[1]
           v == args[2]
       IN IF store[k] # MissingValue
          THEN /\ store' = [store EXCEPT ![k] = v]
               /\ result' = "ok"
          ELSE /\ result' = "error"
               /\ UNCHANGED store
    /\ phase' = "done"
    /\ UNCHANGED <<op, args>>

ProcessDelete ==
    /\ phase = "processing"
    /\ op = "delete"
    /\ LET k == args[1]
       IN store' = [store EXCEPT ![k] = MissingValue]
    /\ result' = "ok"
    /\ phase' = "done"
    /\ UNCHANGED <<op, args>>

Complete ==
    /\ phase = "done"
    /\ op' = "none"
    /\ args' = <<>>
    /\ result' = "none"
    /\ phase' = "idle"
    /\ UNCHANGED store

Request ==
    \E k \in Keys :
        \/ RequestGet(k)
        \/ RequestDelete(k)
        \/ \E v \in Values :
            \/ RequestInsert(k, v)
            \/ RequestUpdate(k, v)

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
    /\ WF_vars(ProcessDelete)
    /\ \A k \in Keys : WF_vars(RequestDelete(k))

Spec == Init /\ [][Next]_vars /\ DeleteFairness

=============================================================================