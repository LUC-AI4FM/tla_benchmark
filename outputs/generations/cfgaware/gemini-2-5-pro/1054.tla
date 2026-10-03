------------------------ MODULE DijkstraTokenRing ------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, M

ASSUME /\ N \in Nat \ {0}  \* At least one node
       /\ M \in Nat \ {0}  \* A non-empty value domain
       /\ N =< M + 1      \* Condition for stabilization

VARIABLES x

\* The set of nodes, identified by 0..N-1.
Nodes == 0..(N-1)

\* The bounded domain of counter values, 0..M-1.
Values == 0..(M-1)

vars == <<x>>

\* Type invariant: the state x is a function from nodes to values.
TypeOK == x \in [Nodes -> Values]

\* The system can start in any arbitrary state, as it is self-stabilizing.
Init == TypeOK

\* The special machine (node 0) has a "privilege" if its value is the same as
\* its predecessor (node N-1). Its action is to increment its value modulo M.
Node0Action ==
    /\ x[0] = x[N-1]
    /\ x' = [x EXCEPT ![0] = (x[0] + 1) % M]

\* Any other machine i has a "privilege" if its value is different from its
\* predecessor (node i-1). Its action is to copy the predecessor's value.
OtherNodeAction(i) ==
    /\ x[i] # x[i-1]
    /\ x' = [x EXCEPT ![i] = x[i-1]]

\* The next-state relation. At each step, one process with a privilege moves.
\* If multiple processes have a privilege, the choice is non-deterministic.
Next ==
    \/ Node0Action
    \/ \E i \in 1..(N-1) : OtherNodeAction(i)

\* The full specification, allowing stuttering steps.
Spec == Init /\ [][Next]_vars

\* A token exists at node i if its value differs from its predecessor's value.
\* For node 0, the predecessor is the last node, N-1.
HasToken(i) ==
    IF i = 0
    THEN x[0] # x[N-1]
    ELSE x[i] # x[i-1]

\* A state is "legitimate" if there is exactly one token in the ring.
UniqueToken ==
    Cardinality({i \in Nodes : HasToken(i)}) = 1

\* The property to check: the system eventually reaches and stays in a
\* legitimate state (a state with a unique token).
Stabilization == <>[]UniqueToken

=============================================================================