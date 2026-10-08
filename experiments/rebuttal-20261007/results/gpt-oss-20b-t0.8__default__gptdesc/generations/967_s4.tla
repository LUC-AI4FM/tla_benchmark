------------------- MODULE StoneCutting -------------------
EXTENDS Naturals, Sequences

CONSTANTS W, N

VARIABLE pieces

\* Sum of the piece weights
operator SumPieces(pieces) ==
    Sum([pieces[i] | i ∈ 1..N])

\* Weighted sum using coefficients {-1,0,1}
operator WeightedSum(coeffs, pieces) ==
    Sum([ coeffs[i] * pieces[i] | i ∈ 1..N ])

\* Every target weight from 1 to W can be represented
operator CanBeWeighted?(pieces) ==
    \A t ∈ 1..W :
        \E coeffs ∈ (1..N -> {-1,0,1}) :
            WeightedSum(coeffs, pieces) = t

Init == pieces ∈ (1..N -> Nat)

Next == UNCHANGED <<pieces>>

Spec == Init /\ []Next

Safety ==
    (\A i ∈ 1..N : pieces[i] > 0)
    /\ SumPieces(pieces) = W
    /\ CanBeWeighted?(pieces)

INVARIANT Safety

\* Dummy definitions to satisfy the use of PrintT in TLC-oriented specifications
operator PrintT(msg, val) == /\ TRUE
operator ShowSolution == PrintT("solution", pieces)