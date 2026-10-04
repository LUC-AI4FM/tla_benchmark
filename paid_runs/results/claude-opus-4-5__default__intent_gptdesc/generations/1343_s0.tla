---------------------------- MODULE ConcurrentPair ----------------------------
EXTENDS Integers

CONSTANTS MinVal, MaxVal

ASSUME MinVal <= 0 /\ MaxVal >= 0

VARIABLES loc1, loc2

vars == <<loc1, loc2>>

TypeOK == /\ loc1 \in MinVal..MaxVal
          /\ loc2 \in MinVal..MaxVal

Init == /\ loc1 = 0
        /\ loc2 = 0

Stutter == UNCHANGED vars

Next == Stutter

Spec == Init /\ [][Next]_vars

\* Initial-state invariant: both locations are zero and equal
InitialStateInvariant == (loc1 = 0) /\ (loc2 = 0) /\ (loc1 = loc2)

\* Equality invariant: the values remain equal in all reachable states
EqualityInvariant == loc1 = loc2

\* Combined safety invariant
SafetyInvariant == /\ TypeOK
                   /\ EqualityInvariant

\* Temporal property: initial condition holds at time 0
InitialConditionHoldsAtStart == InitialStateInvariant

\* Temporal property: all states satisfy equality (since only stuttering is allowed)
AlwaysEqual == []EqualityInvariant

\* Temporal property: values are always unchanged (no transitions modify values)
AlwaysUnchanged == [][UNCHANGED vars]_vars

\* Temporal property: both locations always remain zero
AlwaysZero == [](loc1 = 0 /\ loc2 = 0)

\* Combined temporal specification for correctness
TemporalCorrectness == /\ InitialConditionHoldsAtStart
                       /\ AlwaysEqual
                       /\ AlwaysUnchanged
                       /\ AlwaysZero

===============================================================================