---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals, TLAPS

CONSTANTS N, K

ASSUME NPositive == N > 0
ASSUME KGreaterThanN == K > N

VARIABLES x

vars == <<x>>

Proc == 0..(N-1)

TypeOK == x \in [Proc -> 0..(K-1)]

HasToken(i) ==
    IF i = 0 
    THEN x[i] = x[N-1]
    ELSE x[i] /= x[(i-1)]

TokenCount == Cardinality({i \in Proc : HasToken(i)})

SomeProcessHasToken == \E i \in Proc : HasToken(i)

ExactlyOneToken == Cardinality({i \in Proc : HasToken(i)}) = 1

Init == x \in [Proc -> 0..(K-1)]

Pass0(i) ==
    /\ i = 0
    /\ x[0] = x[N-1]
    /\ x' = [x EXCEPT ![0] = (x[0] + 1) % K]

PassOther(i) ==
    /\ i \in 1..(N-1)
    /\ x[i] /= x[i-1]
    /\ x' = [x EXCEPT ![i] = x[i-1]]

Pass(i) ==
    \/ Pass0(i)
    \/ PassOther(i)

Next == \E i \in Proc : Pass(i)

Fairness == \A i \in Proc : WF_vars(Pass(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Safety == SomeProcessHasToken

Liveness == <>ExactlyOneToken

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OMITTED

THEOREM SafetyHolds == Spec => []Safety
PROOF OMITTED

THEOREM LivenessHolds == Spec => Liveness
PROOF OMITTED

=============================================================================