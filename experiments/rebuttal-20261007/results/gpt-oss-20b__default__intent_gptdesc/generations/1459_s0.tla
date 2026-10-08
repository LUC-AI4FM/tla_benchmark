MODULE Counter
EXTENDS Naturals, TLC

VARIABLE s

Init == s = 0

Inc == /\ s < 3
        /\ s' = s + 1

Stutter == s' = s

Next == Inc \/ Stutter

Spec == Init /\ [][Next]_s

Safety == [] (s \in Nat /\ s <= 3)

Liveness == <> (s = 3)

WFInc == WF(Inc)

SpecFair == Spec /\ WFInc

THEOREM SafetyThm: Spec => Safety
THEOREM LivenessThm: SpecFair => Liveness