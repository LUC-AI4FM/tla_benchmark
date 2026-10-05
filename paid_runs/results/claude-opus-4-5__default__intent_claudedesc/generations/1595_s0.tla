---------------------------- MODULE FairCounter ----------------------------

EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES counter, done

vars == <<counter, done>>

TypeOK == /\ counter \in 0..MaxValue
          /\ done \in BOOLEAN

Init == /\ counter = 0
        /\ done = FALSE

Increment == /\ ~done
             /\ counter < MaxValue
             /\ counter' = counter + 1
             /\ done' = IF counter + 1 = MaxValue THEN TRUE ELSE FALSE

Stutter == /\ done
           /\ UNCHANGED vars

Next == Increment \/ Stutter

Fairness == WF_vars(Increment)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: counter stays within bounds
SafetyInvariant == counter \in 0..MaxValue

\* The counter never exceeds MaxValue
NeverExceedsMax == counter <= MaxValue

\* When done is true, counter must be at MaxValue
DoneImpliesMax == done => counter = MaxValue

\* Termination: the system must eventually reach the done state
Termination == <>(done = TRUE)

\* Termination alternative: counter eventually reaches MaxValue
CounterReachesMax == <>(counter = MaxValue)

\* State uniqueness checks - these can be used with TLC to verify
\* that exactly one state exists with counter = 5
CounterAt5 == counter = 5

\* State where counter = 9 and about to transition to 10
CounterAt9AboutToFinish == counter = 9 /\ ~done

=============================================================================