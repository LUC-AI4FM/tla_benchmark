```tla
MODULE OneVariableSystem

EXTENDS Naturals, Sequences, TLC

CONSTANTS InitValue

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' \in {1, 2}
    \/ /\ x \in {1, 2}
       /\ x' = 0

Spec ==
    INIT Init
    AND [](Next)
    AND WF_x(Next)

-- Temporal properties
StabilizeAwayFromOneOrTwo == <>(x \notin {1, 2})
RepeatedReturnToZero == <>[]<>(x = 0)
NotEventuallyAlwaysNonZero == NOT (<>[](x \in {1, 2}))

-- Postcondition for TLC counterexample trace
VARIABLES trace

CheckTrace ==
    LET actions == [n \in Nat \cup {0} |-> CASE n < Len(trace) -> Elem(trace, n) ELSE <<>>]
    IN /\ InitValue = x
       /\ \A n \in Nat \cup {0} : (actions[n] = <<>>) \/ [][Next]_<<x>>
       /\ NotEventuallyAlwaysNonZero

END MODULE
```