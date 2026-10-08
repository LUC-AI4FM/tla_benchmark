------------------------------- MODULE FischerMutex -------------------------------

CONSTANTS N \* Number of processes
          , Epsilon \* Short delay
          , Delta \* Long delay
          , Infty \* Infinite timer sentinel

ASSUME /\ N \in Nat
       /\ N > 0
       /\ Epsilon \in Nat
       /\ Delta \in Nat
       /\ Epsilon <= Delta

VARIABLES mem \* Shared memory location
          , timers \* Local timers for each process
          , inCS \* Processes currently in the critical section

\* Initial state: shared memory is empty, all timers are infinite, no processes in CS
Init == /\ mem = << >>
        /\ timers = [p \in 1..N -> Infty]
        /\ inCS = {}

\* Action to advance global time (tick)
Tick ==
    /\ \/ timers' = [timers EXCEPT ![p] = IF timers[p] = Infty THEN Infty ELSE timers[p] - 1
       /\ inCS' = inCS

\* Process p tries to enter the critical section
TryEnter(p) ==
    /\ mem = << >>
    /\ timers' = [timers EXCEPT ![p] = Epsilon]
    /\ mem' = <<p>>
    /\ inCS' = inCS

\* Process p enters the critical section if it holds the reservation and timer expired
EnterCS(p) ==
    /\ mem = <<p>>
    /\ timers[p] = 0
    /\ timers' = [timers EXCEPT ![p] = Infty]
    /\ mem' = mem
    /\ inCS' = inCS \cup {p}

\* Process p exits the critical section and clears shared memory
ExitCS(p) ==
    /\ p \in inCS
    /\ timers' = timers
    /\ mem' = << >>
    /\ inCS' = inCS \ {p}

\* Next state relation
Next ==
    \/ Tick
    \/ \E p \in 1..N : TryEnter(p)
    \/ \E p \in 1..N : EnterCS(p)
    \/ \E p \in 1..N : ExitCS(p)

\* Specification: initial state and next-state relation
Spec ==
    /\ Init
    /\ [][Next]_<<mem, timers, inCS>>

\* Invariant: mutual exclusion (no two processes can be in the critical section simultaneously)
Invariant == \/ Cardinality(inCS) <= 1

\* Liveness: strong fairness for each process's entry routine and tick activity
Liveness ==
    /\ \A p \in 1..N : WF_<<mem, timers, inCS>>(TryEnter(p))
    /\ WF_<<mem, timers, inCS>>(Tick)

=============================================================================