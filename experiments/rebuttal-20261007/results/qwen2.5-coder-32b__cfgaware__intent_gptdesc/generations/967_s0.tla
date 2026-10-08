---- MODULE WeighingPieces ----

CONSTANTS W, N

VARIABLES pieces

ASSUME W \in Nat \ {0}
ASSUME N \in Nat \ {0}

(*--algorithm WeighingPieces

variables pieces = << >>;

begin
    Init:
        with newPieces \in [1..N -> 1..W] :
            /\ SUM{i \in 1..N} (newPieces[i]) = W
            /\ pieces' = newPieces;
end algorithm;*)

\* State invariants and properties to check

Invariant ==
    /\ pieces \in [1..N -> Nat]
    /\ (\A i \in 1..N : pieces[i] > 0)
    /\ SUM{i \in 1..N} (pieces[i]) = W

CanAchieveAllTargets ==
    \A t \in 1..W :
        \E coeffs \in [1..N -> {-1, 0, 1}] :
            (\E S \subseteq 1..N :
                /\ SUM{i \in S} (coeffs[i] * pieces[i]) = t)

Spec ==
    Init /\ []Invariant

THEOREM Spec => []CanAchieveAllTargets

====