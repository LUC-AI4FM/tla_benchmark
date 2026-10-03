---------------------------- MODULE dijkstra_token_ring ----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N >= 1
       /\ M >= 1
       /\ N <= M + 1

VARIABLES nodes

vars == <<nodes>>

TypeOK == nodes \in [0..N-1 -> 0..M-1]

Init == nodes \in [0..N-1 -> 0..M-1]

HasToken(i) ==
    IF i = 0
    THEN nodes[i] = nodes[N-1]
    ELSE nodes[i] # nodes[i-1]

TokenCount == Cardinality({i \in 0..N-1 : HasToken(i)})

Cardinality(S) == 
    LET RECURSIVE CardHelper(_)
        CardHelper(T) == IF T = {} THEN 0
                         ELSE 1 + CardHelper(T \ {CHOOSE x \in T : TRUE})
    IN CardHelper(S)

Node0Act ==
    /\ HasToken(0)
    /\ nodes' = [nodes EXCEPT ![0] = (nodes[0] + 1) % M]

NodeIAct(i) ==
    /\ i > 0
    /\ HasToken(i)
    /\ nodes' = [nodes EXCEPT ![i] = nodes[i-1]]

Next ==
    \/ Node0Act
    \/ \E i \in 1..N-1 : NodeIAct(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

UniqueToken == TokenCount = 1

Stabilization == <>[]UniqueToken

===================================================================================