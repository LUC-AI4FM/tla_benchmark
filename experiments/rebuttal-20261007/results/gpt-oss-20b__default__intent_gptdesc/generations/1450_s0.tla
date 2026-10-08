MODULE RandomSubset
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS n, m, k

DOMAIN == 1..n
CODOMAIN == 1..m

Universe == DOMAIN -> CODOMAIN

VARIABLE selected

Init ==
    /\ selected \in SUBSET Universe
    /\ #selected = k

Next ==
    UNCHANGED selected

Spec ==
    Init /\ [][Next]_selected

Inv ==
    (#selected = k) /\ (\A f \in selected : f \in Universe)

THEOREM InvIsInvariant == Spec => []Inv

===============================================================================