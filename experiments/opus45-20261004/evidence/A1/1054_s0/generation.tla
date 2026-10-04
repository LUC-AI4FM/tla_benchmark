---------------------------- MODULE dijkstra ----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N >= 1
       /\ M >= 1
       /\ N <= M + 1

VARIABLES counter

vars == <<counter>>

Nodes == 0..(N-1)
Values == 0..(M-1)

TypeOK == counter \in [Nodes -> Values]

Init == counter \in [Nodes -> Values]

HasToken(i) ==
    IF i = 0
    THEN counter[i] = counter[N-1]
    ELSE counter[i] # counter[i-1]

TokenCount == Cardinality({i \in Nodes : HasToken(i)})

Cardinality(S) ==
    LET CardinalityHelper[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE 1 + CardinalityHelper[T \ {CHOOSE x \in T : TRUE}]
    IN CardinalityHelper[S]

Node0Action ==
    /\ HasToken(0)
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

NodeIAction(i) ==
    /\ i > 0
    /\ HasToken(i)
    /\ counter' = [counter EXCEPT ![i] = counter[i-1]]

Next ==
    \/ Node0Action
    \/ \E i \in 1..(N-1) : NodeIAction(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Stable == TokenCount = 1

Stabilization == <>[]Stable

==========================================================================