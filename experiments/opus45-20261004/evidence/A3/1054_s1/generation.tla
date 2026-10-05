---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME NAssumption == N >= 1
ASSUME MAssumption == M >= 1
ASSUME NMAssumption == N <= M + 1

VARIABLES counter

vars == <<counter>>

Nodes == 0..(N-1)
Values == 0..(M-1)

TypeOK == counter \in [Nodes -> Values]

\* Node 0 has a token when its value equals the last node's value
HasToken0 == counter[0] = counter[N-1]

\* Node i > 0 has a token when its value differs from its predecessor
HasTokenI(i) == counter[i] # counter[i-1]

\* Count the number of tokens in the system
TokenCount == 
    (IF HasToken0 THEN 1 ELSE 0) +
    LET TokensFromOthers == {i \in 1..(N-1) : HasTokenI(i)}
    IN Cardinality(TokensFromOthers)

Cardinality(S) == 
    LET RECURSIVE CardHelper(_, _)
        CardHelper(T, acc) == 
            IF T = {} THEN acc
            ELSE LET x == CHOOSE y \in T : TRUE
                 IN CardHelper(T \ {x}, acc + 1)
    IN CardHelper(S, 0)

\* Alternative: directly compute token count
CountTokens == 
    LET RECURSIVE Count(_, _)
        Count(i, acc) ==
            IF i = N THEN acc
            ELSE IF i = 0 THEN 
                    Count(1, IF counter[0] = counter[N-1] THEN acc + 1 ELSE acc)
                 ELSE 
                    Count(i + 1, IF counter[i] # counter[i-1] THEN acc + 1 ELSE acc)
    IN Count(0, 0)

\* Stable configuration: exactly one token exists
Stable == CountTokens = 1

\* Node 0 action: increment its counter (mod M) when it holds the token
Node0Action ==
    /\ counter[0] = counter[N-1]
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

\* Node i > 0 action: copy predecessor's value when values differ (has token)
NodeIAction(i) ==
    /\ i > 0
    /\ counter[i] # counter[i-1]
    /\ counter' = [counter EXCEPT ![i] = counter[i-1]]

\* Initial state: any configuration (to demonstrate self-stabilization)
Init == counter \in [Nodes -> Values]

\* Next state relation
Next ==
    \/ Node0Action
    \/ \E i \in 1..(N-1) : NodeIAction(i)

\* Fairness: weak fairness for all node actions
Fairness ==
    /\ WF_vars(Node0Action)
    /\ \A i \in 1..(N-1) : WF_vars(NodeIAction(i))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: type correctness
Safety == TypeOK

\* Liveness property: eventually the system stabilizes and stays stable
\* (eventually always exactly one token)
Stabilization == <>[]Stable

===============================================================================