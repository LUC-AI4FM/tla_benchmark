---------------------------- MODULE BoundedCounter ----------------------------
EXTENDS Naturals

CONSTANT Bound

ASSUME BoundAssumption == Bound \in Nat /\ Bound > 0

VARIABLE counter

vars == <<counter>>

TypeOK == counter \in Nat

Init == counter = 0

CanIncrement == counter + 1 < Bound

Increment ==
    /\ CanIncrement
    /\ counter' = counter + 1

Halt ==
    /\ ~CanIncrement
    /\ UNCHANGED counter

Next == Increment \/ Halt

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

BoundInvariant == counter < Bound

Safety == TypeOK /\ BoundInvariant

NoDeadlock == ENABLED Next

IncrementEnabledBelowLimit == CanIncrement => ENABLED Increment

Progress ==
    \A k \in 0..(Bound - 2) : (counter = k) ~> (counter = k + 1)

EventuallyReachesLimit == <>(counter = Bound - 1)

EventuallyStable == <>[](counter = Bound - 1)

Monotonic == [][counter' >= counter]_vars

StepByOne == [][counter' = counter + 1]_vars

THEOREM Spec => []Safety
THEOREM Spec => []IncrementEnabledBelowLimit
THEOREM Spec => Progress /\ EventuallyReachesLimit /\ EventuallyStable
=============================================================================