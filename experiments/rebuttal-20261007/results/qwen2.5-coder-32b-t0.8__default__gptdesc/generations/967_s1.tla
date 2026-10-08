------------------------------- MODULE StoneCutting ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS W, N

VARIABLES pieces

Init == /\ pieces \in Seq(Naturals)
        /\ Len(pieces) = N
        /\ Sum(pieces) = W

Next ==
    LET nextPieces == Choose(s \in [1..N -> Naturals] : Len(s) = N /\ Sum(s) = W)
    IN  \/ /\ pieces' = nextPieces
        \/ /\ pieces' = pieces

Spec == Init /\ [][Next]_<<pieces>>

Correctness ==
    \A target \in 1..W :
        \E coeffs \in [1..N -> {-1, 0, 1}] :
            Sum({i \in 1..N : coeffs[i] # 0} : pieces[i] * coeffs[i]) = target

Invariants == Correctness

Liveness ==
    <>[](Correctness \/ PrintT("No solution exists"))

Fairness == WF_vars(<<pieces>>)

THEOREM Spec => []Invariants
THEOREM Spec /\ Fairness => Liveness

=============================================================================