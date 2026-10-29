---- MODULE IntegerDecrementCounter ----
EXTENDS Naturals, Integers

VARIABLE x

vars == << x >>

TypeOK == x \in {-1, -2, -3}

Init == x = -1

Decrement ==
    /\ x > -3
    /\ x' = x - 1

Stutter ==
    /\ x = -3
    /\ UNCHANGED x

Next == Decrement \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Decrement)

\* Safety: the counter never goes below -3 and never exceeds -1
Bounded == x >= -3 /\ x <= -1

\* Safety: the counter never increases
NeverIncreases == [][x' <= x]_vars

\* Safety: once at -3, it stays at -3
StaysAtStop == [](x = -3 => [](x = -3))

\* Liveness: the counter eventually reaches -3 and remains there
EventuallyStops == <>[](x = -3)

====