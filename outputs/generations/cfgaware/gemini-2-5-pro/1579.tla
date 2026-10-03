---- MODULE DijkstraTokenRing ----
EXTENDS Integers

CONSTANTS N, K
ASSUME N \in Nat \ {0} /\ K > N

VARIABLES x

Procs == 0..(N-1)

\* The predecessor of process i in the ring.
Pred(i) == (i - 1 + N) % N

\* A process i is privileged (holds a token) if its value differs from its predecessor's.
IsPrivileged(i) == x[i] # x[Pred(i)]

\* The number of privileged processes (token holders).
NumPrivileged == Cardinality({i \in Procs : IsPrivileged(i)})

\* The type invariant: each process has a value in 0..(K-1).
TypeOK == x \in [Procs -> 0..(K-1)]

\* Initial state: the system can start in any arbitrary configuration.
Init == TypeOK

\* Action for a non-special process i (i > 0). If its value is different
\* from its predecessor, it copies the predecessor's value.
P(i) == /\ i \in 1..(N-1)
        /\ x[i] # x[Pred(i)]
        /\ x' = [x EXCEPT ![i] = x[Pred(i)]]

\* Action for the special process 0. If its value is the same as its
\* predecessor, it increments its value modulo K.
P0 == /\ x[0] = x[Pred(0)]
      /\ x' = [x EXCEPT ![0] = (x[0] + 1) % K]

\* The next-state relation.
Next == P0 \/ (\E i \in 1..(N-1) : P(i))

\* The fairness condition: weak fairness for every process action.
Fairness == WF_x(P0) /\ \A i \in 1..(N-1) : WF_x(P(i))

\* The full temporal specification.
Spec == Init /\ [][Next]_x /\ Fairness

\* Property: There is always at least one token holder.
\* This is not true in all initial states (e.g., all x[i] are equal),
\* but becomes true after the first step of process 0.
SomeoneHoldsToken == NumPrivileged > 0

\* Property: The system eventually converges to a state with exactly one token.
EventuallyJustOneHoldsToken == []<>(NumPrivileged = 1)

=============================================================================