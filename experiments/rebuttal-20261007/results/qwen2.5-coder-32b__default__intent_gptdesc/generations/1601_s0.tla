------------------------------- MODULE FischerMutex -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, LONG_DELAY, SHORT_DELAY, INFINITE_TIMER

VARIABLES sharedMemory, timers, inCS

Init == /\ sharedMemory = << >>
        /\ timers = [p \in 1..N -> INFINITE_TIMER]
        /\ inCS = {}

Next ==
    \/ \E p \in 1..N \ (DOMAIN inCS) :
         /\ timers[p] = INFINITE_TIMER
         /\ sharedMemory = << >>
         /\ sharedMemory' = <<p>>
         /\ timers' = [timers EXCEPT ![p] = SHORT_DELAY]
         /\ inCS' = inCS
    \/ \E p \in 1..N :
         /\ timers[p] > 0
         /\ timers' = [timers EXCEPT ![p] = timers[p] - 1]
         /\ sharedMemory' = sharedMemory
         /\ inCS' = inCS
    \/ \E p \in 1..N :
         /\ timers[p] = 0
         /\ sharedMemory = <<p>>
         /\ sharedMemory' = << >>
         /\ timers' = [timers EXCEPT ![p] = INFINITE_TIMER]
         /\ inCS' = inCS \cup {p}
    \/ \E p \in 1..N :
         /\ p \in inCS
         /\ sharedMemory' = sharedMemory
         /\ timers' = timers
         /\ inCS' = inCS \ {p}

Spec ==
    /\ Init
    /\ [][Next]_<<sharedMemory, timers, inCS>>
    /\ WF_next(<<sharedMemory, timers, inCS>>)

MutualExclusion == \/ inCS = {}
                     \/ Cardinality(inCS) = 1

Liveness ==
    \A p \in 1..N :
        <>[](p \notin inCS => <>[]p \in inCS)

Fairness ==
    WF_next(<<sharedMemory, timers, inCS>>)
    /\ SF_next(<<sharedMemory, timers, inCS>>, {p \in 1..N : p \notin inCS})

=============================================================================