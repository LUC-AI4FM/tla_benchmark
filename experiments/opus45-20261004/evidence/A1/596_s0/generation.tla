---------------------------- MODULE spec ----------------------------

VARIABLE x

Init == x = 0

Next == 
    \/ (x = 0 /\ (x' = 1 \/ x' = 2))
    \/ (x /= 0 /\ x' = 0)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

EventuallyNot1 == <>(x /= 1)

EventuallyNot2 == <>(x /= 2)

AlwaysEventuallyZero == []<>(x = 0)

NotAlwaysEventuallyZero == ~AlwaysEventuallyZero

TracePostCondition ==
    LET trace == <<[x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2], [x |-> 0]>>
        states == {trace[i] : i \in 1..Len(trace)}
    IN x \in {r.x : r \in states}

=============================================================================