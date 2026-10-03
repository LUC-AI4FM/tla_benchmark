------------------ MODULE DijkstraTokenRing ------------------
EXTENDS Naturals, TLC

CONSTANTS N, K

ASSUME  /\ N \in Nat
        /\ N > 0
        /\ K \in Nat
        /\ K > N

VARIABLES x

Procs == 0..(N-1)
Range == 0..(K-1)
vars == <<x>>

\* The predecessor of process i in the ring.
pred(i) == IF i = 0 THEN N-1 ELSE i-1

\* A process i is privileged (holds a token) if its state enables it to move.
\* Process 0 is privileged if its value equals its predecessor's.
\* Any other process i is privileged if its value is different from its predecessor's.
Privileged(i) ==
    IF i = 0
    THEN x[0] = x[pred(0)]
    ELSE x[i] # x[pred(i)]

\* The action of process 0: increment its value modulo K.
MoveP0 ==
    /\ Privileged(0)
    /\ x' = [x EXCEPT ![0] = (x[0] + 1) % K]

\* The action of a process i > 0: copy the value of its predecessor.
MovePi(i) ==
    /\ i \in 1..(N-1)
    /\ Privileged(i)
    /\ x' = [x EXCEPT ![i] = x[pred(i)]]

\* The atomic action of an arbitrary process i.
Move(i) ==
    IF i = 0 THEN MoveP0 ELSE MovePi(i)

\* The system starts in any arbitrary state.
Init == x \in [Procs -> Range]

\* The next-state relation: some privileged process makes a move.
Next == \E i \in Procs : Move(i)

\* The specification requires weak fairness for every process.
\* If a process is continuously or repeatedly privileged, it must eventually move.
Fairness == \A i \in Procs : WF_vars(Move(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\*-----------------------------------------------------------------------------
\* PROPERTIES
\*-----------------------------------------------------------------------------

\* Safety Invariant: At least one process is always privileged.
\* The negation of this is that for all i, ~Privileged(i), which implies:
\* x[0] # x[N-1] AND x[1] = x[0] AND x[2] = x[1] ... AND x[N-1] = x[N-2].
\* This simplifies to x[0] = x[1] = ... = x[N-1], which contradicts x[0] # x[N-1].
\* Therefore, this is an invariant.
SomePrivileged == \E i \in Procs : Privileged(i)
THEOREM Spec => []SomePrivileged

\* A state is "legitimate" if exactly one process is privileged.
IsLegitimate == Cardinality({i \in Procs : Privileged(i)}) = 1

\* Liveness Property: The system eventually converges to a legitimate state
\* where exactly one token exists, and remains in such a state.
Convergence == <>([]IsLegitimate)
THEOREM Spec => Convergence

=============================================================================