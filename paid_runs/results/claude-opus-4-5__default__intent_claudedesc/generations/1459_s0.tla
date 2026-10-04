---------------------------- MODULE TraceExpressionDemo ----------------------------
EXTENDS Integers

CONSTANTS Bound

VARIABLES counter

Init == counter = 0

Increment == 
    /\ counter < Bound
    /\ counter' = counter + 1

Stutter ==
    /\ counter = Bound
    /\ counter' = counter

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_counter

\* Safety invariant: counter stays within valid range
CounterInRange == counter >= 0 /\ counter <= Bound

\* Safety invariant: counter never exceeds the bound
NeverExceedsBound == counter <= Bound

\* Type invariant
TypeOK == counter \in 0..Bound

\* Liveness property: counter eventually reaches the bound
EventuallyReachesBound == <>(counter = Bound)

\* Liveness property: once at bound, stays at bound
StaysAtBound == [](counter = Bound => [](counter = Bound))

\* Specification with weak fairness to ensure progress
FairSpec == Spec /\ WF_counter(Increment)

===================================================================================