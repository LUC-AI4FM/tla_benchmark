---------------------------- MODULE spec ----------------------------

VARIABLE x

Init == x = 0

Next == 
    \/ (x = 0 /\ (x' = 1 \/ x' = 2))
    \/ (x /= 0 /\ x' = 0)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

EventuallyNotOne == <>(x /= 1)

EventuallyNotTwo == <>(x /= 2)

AlwaysEventuallyZero == []<>(x = 0)

NegatedProperty == ~AlwaysEventuallyZero

TracePostCondition ==
    LET trace == <<[x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2], [x |-> 0]>>
        validStates == {0, 1, 2}
    IN \A i \in 1..Len(trace) : trace[i].x \in validStates

=============================================================================