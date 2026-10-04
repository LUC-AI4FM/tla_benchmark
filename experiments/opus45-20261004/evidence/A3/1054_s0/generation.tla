---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals, TLAPS

CONSTANTS N, M

ASSUME NAssumption == N >= 1
ASSUME MAssumption == M >= 1
ASSUME NMAssumption == N <= M + 1

Nodes == 0..(N-1)
Values == 0..(M-1)

VARIABLES counter

TypeInvariant == counter \in [Nodes -> Values]

\* Node 0 has a token if its value equals the value of the last node (N-1)
\* Other nodes have a token if their value differs from their predecessor
HasToken(i) ==
    IF i = 0
    THEN counter[i] = counter[N-1]
    ELSE counter[i] # counter[i-1]

\* Count the number of tokens in the system
TokenCount == Cardinality({i \in Nodes : HasToken(i)})

\* The system is stable when there is exactly one token
Stable == TokenCount = 1

\* Node 0 action: increment counter modulo M when it has a token
Node0Action ==
    /\ HasToken(0)
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

\* Other node action: copy predecessor's value when values differ (has token)
NodeIAction(i) ==
    /\ i > 0
    /\ HasToken(i)
    /\ counter' = [counter EXCEPT ![i] = counter[i-1]]

\* Initial state: any configuration of counter values
Init == counter \in [Nodes -> Values]

\* Next state: either node 0 acts or some other node acts
Next ==
    \/ Node0Action
    \/ \E i \in Nodes \ {0} : NodeIAction(i)

\* Fairness: weak fairness on all node actions
Fairness ==
    /\ WF_counter(Node0Action)
    /\ \A i \in Nodes \ {0} : WF_counter(NodeIAction(i))

\* Full specification with fairness
Spec == Init /\ [][Next]_counter /\ Fairness

\* Safety invariant: type correctness is always maintained
Safety == TypeInvariant

\* Helper: Cardinality function for finite sets
RECURSIVE Cardinality(_)
Cardinality(S) ==
    IF S = {} THEN 0
    ELSE 1 + Cardinality(S \ {CHOOSE x \in S : TRUE})

\* Liveness property: eventually the system stabilizes and stays stable
\* (eventually always exactly one token)
Stabilization == <>[]Stable

\* Alternative formulation: eventually reaches a stable state
EventuallyStable == <>Stable

=============================================================================