---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Integers, Naturals, TLAPS

CONSTANTS N, K

ASSUME NPositive == N > 0
ASSUME KGreaterThanN == K > N

VARIABLES x

vars == <<x>>

TypeOK == x \in [0..(N-1) -> 0..(K-1)]

HasToken(i) ==
    IF i = 0
    THEN x[i] = x[N-1]
    ELSE x[i] # x[i-1]

TokenCount == Cardinality({i \in 0..(N-1) : HasToken(i)})

Cardinality(S) == 
    LET Card[T \in SUBSET (0..(N-1))] ==
        IF T = {} THEN 0
        ELSE 1 + Card[T \ {CHOOSE t \in T : TRUE}]
    IN Card[S]

Process0 ==
    /\ x[0] = x[N-1]
    /\ x' = [x EXCEPT ![0] = (x[0] + 1) % K]

ProcessI(i) ==
    /\ i \in 1..(N-1)
    /\ x[i] # x[i-1]
    /\ x' = [x EXCEPT ![i] = x[i-1]]

Init == x \in [0..(N-1) -> 0..(K-1)]

Next ==
    \/ Process0
    \/ \E i \in 1..(N-1) : ProcessI(i)

Fairness ==
    /\ WF_vars(Process0)
    /\ \A i \in 1..(N-1) : WF_vars(ProcessI(i))

Spec == Init /\ [][Next]_vars /\ Fairness

SomeProcessHasToken == \E i \in 0..(N-1) : HasToken(i)

ExactlyOneToken == 
    \E i \in 0..(N-1) : 
        /\ HasToken(i)
        /\ \A j \in 0..(N-1) : j # i => ~HasToken(j)

Legitimate == ExactlyOneToken

Safety == []SomeProcessHasToken

Liveness == <>Legitimate

Convergence == <>[]Legitimate

THEOREM TypeCorrectness == Spec => []TypeOK

THEOREM SafetyProperty == Spec => Safety

THEOREM LivenessProperty == Spec => Liveness

THEOREM ConvergenceProperty == Spec => Convergence

=============================================================================