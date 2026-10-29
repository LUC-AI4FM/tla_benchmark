------------------------------- MODULE Counter -------------------------------
EXTENDS Naturals

\* Parameters: the target value and the upper bound.
\* They are defined as operators so the module binds to a fixed configuration.
\* Edit these definitions to change the parameters.
Target == 3
Bound  == 5

ASSUME Target \in Nat /\ Bound \in Nat /\ Target <= Bound

VARIABLES x, result

vars == <<x, result>>

TypeOK ==
    /\ x \in 0..Bound
    /\ result \in BOOLEAN

Init ==
    /\ x = 0
    /\ result = (x = Target)

\* Increment: only if strictly below the upper bound. It leaves result unchanged.
Inc ==
    /\ x < Bound
    /\ x' = x + 1
    /\ UNCHANGED result

\* Reset: set the counter back to zero.
Reset ==
    /\ x' = 0
    /\ UNCHANGED result

\* Test: check whether the counter equals the target, without modifying it.
Test ==
    /\ result' = (x = Target)
    /\ UNCHANGED x

Next == Inc \/ Reset \/ Test

Spec == Init /\ [][Next]_vars /\ WF_vars(Inc)

-----------------------------------------------------------------------------
\* Safety properties

\* The counter is always a natural number and never exceeds the bound.
CounterInRange == x \in Nat /\ x <= Bound

TypeInvariant == TypeOK

\* A test step yields true exactly when the counter equals the target.
TestCorrect == [][Test => result' = (x = Target)]_vars

\* An increment does not change the observed test result.
IncPreservesResult == [][Inc => result' = result]_vars

\* The counter changes only by +1 (increment) or to 0 (reset).
CounterSteps == [][x' = x + 1 \/ x' = 0 \/ x' = x]_vars

-----------------------------------------------------------------------------
\* Liveness properties

\* From below the target, the target is eventually reached by increments,
\* unless resets keep intervening forever.
ReachTarget ==
    ([]<><<Reset>>_vars) \/ ((x < Target) ~> (x = Target))

\* No deadlock: some operation is always enabled.
NoDeadlock == [](ENABLED Next)

=============================================================================