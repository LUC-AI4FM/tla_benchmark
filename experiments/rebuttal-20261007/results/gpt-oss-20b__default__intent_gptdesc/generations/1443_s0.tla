MODULE CyclicCounter
EXTENDS Naturals

VARIABLE s

vars == <<s>>

Init == s = 0

Next ==
    \/ (s'=1 /\ s=0)
    \/ (s'=2 /\ s=1)
    \/ (s'=0 /\ s=2)

Spec == Init /\ [][Next]_vars

SafetyInvariant == s \in {0,1,2}

Deterministic == [] (Next => (s' = Mod(s+1,3)))

Reachable1 == <> (s=1)
Reachable2 == <> (s=2)

WrapAction == s=2 /\ s'=0
WrapOnce == <> WrapAction

CycleLiveness == []<>(s=0) /\ []<>(s=1) /\ []<>(s=2)