---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals, TLAPS

CONSTANTS N, M

ASSUME NAssumption == N >= 1
ASSUME MAssumption == M >= 1
ASSUME NMAssumption == N <= M + 1

Nodes == 0..(N-1)
Values == 0..(M-1)

VARIABLE counter

TypeInvariant == counter \in [Nodes -> Values]

HasToken(i) ==
    IF i = 0
    THEN counter[0] = counter[N-1]
    ELSE counter[i] # counter[i-1]

TokenCount == Cardinality({i \in Nodes : HasToken(i)})

UniqueToken == TokenCount = 1

Stabilized == \E i \in Nodes : HasToken(i) /\ \A j \in Nodes : j # i => ~HasToken(j)

Init == counter \in [Nodes -> Values]

Node0Action ==
    /\ HasToken(0)
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

NodeIAction(i) ==
    /\ i # 0
    /\ HasToken(i)
    /\ counter' = [counter EXCEPT ![i] = counter[i-1]]

Next == 
    \/ Node0Action
    \/ \E i \in Nodes \ {0} : NodeIAction(i)

Fairness == WF_counter(Next)

Spec == Init /\ [][Next]_counter /\ Fairness

AtLeastOneToken == \E i \in Nodes : HasToken(i)

SafetyInvariant == TypeInvariant

Stabilization == <>[]UniqueToken

===================================================================================