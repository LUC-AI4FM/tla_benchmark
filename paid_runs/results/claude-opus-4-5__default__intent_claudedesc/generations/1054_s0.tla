-------------------------------- MODULE EWD426 --------------------------------
\* Dijkstra's self-stabilizing token ring algorithm (EWD426)
\* A ring of N nodes where each node holds a counter value in domain 0..M-1
\* The token is defined implicitly by relationships between neighboring counters

EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NConstraint == N \in Nat \ {0}
ASSUME MConstraint == M \in Nat \ {0}
ASSUME NMConstraint == N <= M + 1

VARIABLES counter

vars == <<counter>>

Nodes == 0..(N-1)
Values == 0..(M-1)

\* Predecessor of node i in the ring
Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

\* Node 0 is privileged when its counter equals its predecessor's counter
\* (predecessor of 0 is N-1)
Privileged0 == counter[0] = counter[N-1]

\* Node i (i > 0) is privileged when its counter differs from its predecessor's
PrivilegedOther(i) == counter[i] # counter[Pred(i)]

\* Check if node i is privileged
IsPrivileged(i) == IF i = 0 THEN Privileged0 ELSE PrivilegedOther(i)

\* The set of all privileged nodes
PrivilegedNodes == {i \in Nodes : IsPrivileged(i)}

\* Action for node 0: increment counter modulo M when privileged
Move0 == 
    /\ Privileged0
    /\ counter' = [counter EXCEPT ![0] = (counter[0] + 1) % M]

\* Action for node i > 0: copy predecessor's counter when privileged
MoveOther(i) ==
    /\ i \in 1..(N-1)
    /\ PrivilegedOther(i)
    /\ counter' = [counter EXCEPT ![i] = counter[Pred(i)]]

\* Combined move action for any node i
Move(i) == IF i = 0 THEN Move0 ELSE MoveOther(i)

\* Type invariant
TypeOK == counter \in [Nodes -> Values]

\* Initial state: any arbitrary configuration
Init == counter \in [Nodes -> Values]

\* Next state: some privileged node moves
Next == \E i \in Nodes : Move(i)

\* Weak fairness on all node transitions
Fairness == \A i \in Nodes : WF_vars(Move(i))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY AND LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* Count the number of tokens (privileged nodes)
TokenCount == Cardinality(PrivilegedNodes)

\* Safety: There is always at least one privileged node (the system never deadlocks)
\* This is a known property of Dijkstra's algorithm
AtLeastOneToken == TokenCount >= 1

\* A legitimate (stable) configuration has exactly one token
ExactlyOneToken == TokenCount = 1

\* In a legitimate state, there exists a unique position k where the token is:
\* - All nodes from 0 to k-1 have the same value as node 0
\* - All nodes from k to N-1 have value (counter[0] - 1) mod M
\* The token is at position k (where the transition occurs)
LegitimateState ==
    \E k \in Nodes :
        LET v0 == counter[0]
            vPrev == (v0 + M - 1) % M
        IN /\ \A i \in 0..(k-1) : counter[i] = v0
           /\ IF k < N - 1 
              THEN \A i \in k..(N-1) : counter[i] = vPrev
              ELSE TRUE
           /\ IF k = 0 
              THEN counter[N-1] = v0  \* Token at node 0: pred equals node 0
              ELSE counter[k] # counter[k-1]  \* Token at node k > 0

\* Alternative characterization: exactly one token exists
\* This is equivalent to ExactlyOneToken
OneTokenExists == 
    Cardinality({i \in Nodes : IsPrivileged(i)}) = 1

\* LIVENESS: The system eventually stabilizes to exactly one token
\* This is the main correctness property of Dijkstra's algorithm
Stabilization == <>[]ExactlyOneToken

\* Once stabilized, the system remains stable (one token circulates)
\* This follows from the algorithm design but we state it explicitly
StableOnceReached == [](ExactlyOneToken => []ExactlyOneToken)

\* The token eventually visits every node (liveness under fairness)
\* Node i eventually becomes privileged
EventuallyPrivileged(i) == <>IsPrivileged(i)

\* All nodes are eventually privileged (token circulation)
TokenCirculates == \A i \in Nodes : []<>IsPrivileged(i)

================================================================================