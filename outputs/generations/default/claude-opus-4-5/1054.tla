---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals, Integers

CONSTANTS N, M

ASSUME NAssumption == N >= 1
ASSUME MAssumption == M >= 1
ASSUME NMAssumption == N <= M + 1

VARIABLES counter

vars == <<counter>>

Nodes == 0..(N-1)
Values == 0..(M-1)

TypeOK == counter \in [Nodes -> Values]

\* Node i has the token if its value differs from its predecessor (mod N)
\* For node 0, predecessor is node N-1
\* For other nodes, predecessor is node i-1
HasToken(i) ==
    IF i = 0
    THEN counter[i] = counter[N-1]
    ELSE counter[i] # counter[i-1]

\* Count the number of tokens in the system
TokenCount == Cardinality({i \in Nodes : HasToken(i)})

\* The system has exactly one token
UniqueToken == TokenCount = 1

\* Node 0 action: can create a new token by incrementing when it equals node N-1
Node0Action ==
    /\ counter[0] = counter[N-1]
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

\* Other node action: passes token by copying predecessor when values differ
OtherNodeAction(i) ==
    /\ i > 0
    /\ counter[i] # counter[i-1]
    /\ counter' = [counter EXCEPT ![i] = counter[i-1]]

\* Helper to count tokens (using recursive function)
RECURSIVE CountTokens(_)
CountTokens(S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN (IF HasToken(x) THEN 1 ELSE 0) + CountTokens(S \ {x})

Init == counter \in [Nodes -> Values]

Next ==
    \/ Node0Action
    \/ \E i \in 1..(N-1) : OtherNodeAction(i)

\* Fairness: weak fairness on all actions
Fairness ==
    /\ WF_vars(Node0Action)
    /\ \A i \in 1..(N-1) : WF_vars(OtherNodeAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: type correctness
Safety == TypeOK

\* Liveness property: eventually the system reaches and stays in a state with unique token
Stabilization == <>[]UniqueToken

===================================================================================