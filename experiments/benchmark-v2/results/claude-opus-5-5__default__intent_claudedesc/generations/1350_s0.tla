---- MODULE CounterLeadsToStable ----
EXTENDS Naturals

CONSTANT Max

ASSUME Max = 5

VARIABLE x

vars == << x >>

Init == x = 1

Increment ==
    /\ x < Max
    /\ x' = x + 1

Next == Increment

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in 1..Max

Bounded == x <= Max

Monotonic == [][x' >= x]_vars

EventuallyMax == <>(x = Max)

StableAtMax == [](x = Max => [](x = Max))

LeadsToStable == (x = 1) ~> [](x = Max)

Liveness == <>[](x = Max)

THEOREM Spec => []TypeOK
THEOREM Spec => LeadsToStable
====