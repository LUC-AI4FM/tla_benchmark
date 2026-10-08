---------------------------- MODULE spec ----------------------------

EXTENDS Naturals

CONSTANT Bound

VARIABLE counter, state

vars == <<counter, state>>

TypeOK == counter \in 0..Bound /\ state \in {"running", "terminated"}

Init == counter = 0 /\ state = "running"

Increment == 
    /\ state = "running"
    /\ counter < Bound
    /\ counter' = counter + 1
    /\ IF counter' = Bound 
       THEN state' = "terminated"
       ELSE state' = "running"

Idle ==
    /\ state = "terminated"
    /\ UNCHANGED vars

Next == Increment \/ Idle

Fairness == WF_vars(Increment)

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(state = "terminated")

SafetyNoDecrease == [][counter' >= counter]_vars

SafetyIncrementByOne == [][counter' = counter \/ counter' = counter + 1]_vars

Safety == SafetyNoDecrease /\ SafetyIncrementByOne

Progress == <>(counter = Bound)

CanReachFive == <>(counter = 5)

CanTransitionNineToTen == <>(counter = 9) ~> (counter = 10)

PenultimateToFinalAtomic == 
    []((counter = 9 /\ state = "running") => <>(counter = 10))

=============================================================================