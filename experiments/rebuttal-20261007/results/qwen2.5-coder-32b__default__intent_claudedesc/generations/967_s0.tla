------------------------------- MODULE StonePartition -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS W, N

VARIABLES partition

Init == /\ partition \in SUBSET [1..N -> Nat]
        /\ Sum(partition) = W
        /\ \A i \in 1..N-1 : partition[i] <= partition[i+1]

Next ==
    LET nextPartition == Choose(p \in SUBSET [1..N -> Nat] :
                                Sum(p) = W
                                /\ \A i \in 1..N-1 : p[i] <= p[i+1]
                                /\ p /= partition)
    IN  \/ /\ partition = << >>
            /\ nextPartition = << >>
        \/ /\ partition \in SUBSET [1..N -> Nat]
           /\ nextPartition \in SUBSET [1..N -> Nat]
           /\ Sum(nextPartition) = W
           /\ \A i \in 1..N-1 : nextPartition[i] <= nextPartition[i+1]
           /\ nextPartition /= partition

Spec == Init /\ [][Next]_<<partition>>

Invariant ==
    \/ \E p \in SUBSET [1..N -> Nat] :
         Sum(p) = W
         /\ \A i \in 1..N-1 : p[i] <= p[i+1]
         /\ \A w \in 1..W : \E coeffs \in [1..N -> {-1, 0, 1}] :
              \Sum{i \in 1..N} (coeffs[i] * p[i]) = w
    \/ partition = << >>

Fairness == WF_next(Next)

=============================================================================