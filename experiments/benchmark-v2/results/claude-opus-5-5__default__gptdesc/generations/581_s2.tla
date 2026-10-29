------------------------------- MODULE MCSingleNode -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ---------------------------------------------------------------------------
\* Base single-node specification (inlined so the module is self-contained)
\* ---------------------------------------------------------------------------

CONSTANTS Keys, Values, HistoryLimit

ASSUME HistoryLimit \in Nat

VARIABLES store, durable, up, history

vars == <<store, durable, up, history>>

NoValue == CHOOSE v : v \notin Values

Event == [type : {"write"}, key : Keys, value : Values]
    \cup [type : {"read"}, key : Keys, value : Values \cup {NoValue}]
    \cup [type : {"flush"}]

TypeOK ==
    /\ store \in [Keys -> Values \cup {NoValue}]
    /\ durable \in [Keys -> Values \cup {NoValue}]
    /\ up \in BOOLEAN
    /\ history \in Seq(Event)

Init ==
    /\ store = [k \in Keys |-> NoValue]
    /\ durable = [k \in Keys |-> NoValue]
    /\ up = TRUE
    /\ history = << >>

Write(k, v) ==
    /\ up
    /\ store' = [store EXCEPT ![k] = v]
    /\ history' = Append(history, [type |-> "write", key |-> k, value |-> v])
    /\ UNCHANGED <<durable, up>>

Read(k) ==
    /\ up
    /\ history' = Append(history, [type |-> "read", key |-> k, value |-> store[k]])
    /\ UNCHANGED <<store, durable, up>>

Flush ==
    /\ up
    /\ durable' = store
    /\ history' = Append(history, [type |-> "flush"])
    /\ UNCHANGED <<store, up>>

Crash ==
    /\ up
    /\ up' = FALSE
    /\ UNCHANGED <<store, durable, history>>

Restart ==
    /\ ~up
    /\ up' = TRUE
    /\ store' = durable
    /\ UNCHANGED <<durable, history>>

\* ---------------------------------------------------------------------------
\* Bounded model-checking wrapper
\* ---------------------------------------------------------------------------

HistoryBound == Len(history) < HistoryLimit

BoundedWrite(k, v) ==
    /\ HistoryBound
    /\ Write(k, v)

BoundedRead(k) ==
    /\ HistoryBound
    /\ Read(k)

BoundedFlush ==
    /\ HistoryBound
    /\ Flush

BoundedNext ==
    \/ \E k \in Keys, v \in Values : BoundedWrite(k, v)
    \/ \E k \in Keys : BoundedRead(k)
    \/ BoundedFlush
    \/ Crash
    \/ Restart

Spec == Init /\ [][BoundedNext]_vars

\* ---------------------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------------------

HistoryWithinLimit == Len(history) <= HistoryLimit

==================================================================================