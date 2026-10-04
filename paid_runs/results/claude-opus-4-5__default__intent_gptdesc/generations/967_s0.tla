---------------------------- MODULE WeighingPieces ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS W, N

ASSUME WPositive == W \in Nat \ {0}
ASSUME NPositive == N \in Nat \ {0}

VARIABLES pieces

\* Helper: Generate all sequences of length n with elements from set S
SeqsOfLength(S, n) ==
    IF n = 0 THEN {<<>>}
    ELSE {<<s>> \o rest : s \in S, rest \in SeqsOfLength(S, n-1)}

\* Generate all partitions of total W into N positive integer pieces (non-decreasing order)
\* A partition is represented as a sequence of length N with pieces[1] <= pieces[2] <= ... <= pieces[N]
PartitionsHelper(remaining, numPieces, minVal) ==
    IF numPieces = 0 THEN
        IF remaining = 0 THEN {<<>>} ELSE {}
    ELSE IF numPieces = 1 THEN
        IF remaining >= minVal THEN {<<remaining>>} ELSE {}
    ELSE
        UNION {
            {<<v>> \o rest : rest \in PartitionsHelper(remaining - v, numPieces - 1, v)}
            : v \in minVal..remaining \div numPieces
        }

Partitions == PartitionsHelper(W, N, 1)

\* Sum of elements in a sequence
SeqSum(seq) ==
    IF seq = <<>> THEN 0
    ELSE LET RECURSIVE SumHelper(_)
             SumHelper(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumHelper(Tail(s))
         IN SumHelper(seq)

\* Check if a sequence is non-decreasing (canonical form for multiset)
IsNonDecreasing(seq) ==
    \A i \in 1..(Len(seq)-1) : seq[i] <= seq[i+1]

\* All possible coefficient assignments: each piece gets -1, 0, or 1
\* Coefficients is a sequence of length N with values in {-1, 0, 1}
Coefficients == SeqsOfLength({-1, 0, 1}, N)

\* Compute the weighted sum given pieces and coefficients
\* coeff[i] = 1 means piece i on target pan, -1 means on other pan, 0 means unused
WeightedSum(p, coeff) ==
    LET RECURSIVE WSHelper(_, _)
        WSHelper(idx, acc) ==
            IF idx > N THEN acc
            ELSE WSHelper(idx + 1, acc + coeff[idx] * p[idx])
    IN WSHelper(1, 0)

\* Check if target t can be achieved with the given pieces
\* We need: sum of (coeff[i] * pieces[i]) = t for some coeff in {-1,0,1}^N
CanAchieve(p, t) ==
    \E coeff \in Coefficients : WeightedSum(p, coeff) = t

\* Check if all targets from 1 to W can be achieved
AllTargetsAchievable(p) ==
    \A t \in 1..W : CanAchieve(p, t)

\* Type invariant: pieces is a valid partition representation
TypeOK ==
    /\ pieces \in Seq(Nat \ {0})
    /\ Len(pieces) = N

\* Invariant: All piece weights are positive integers
PiecesPositive ==
    \A i \in 1..N : pieces[i] \in Nat \ {0}

\* Invariant: Pieces sum to W
PiecesSumToW ==
    SeqSum(pieces) = W

\* Invariant: Pieces are in canonical (non-decreasing) order
PiecesCanonical ==
    IsNonDecreasing(pieces)

\* Property: All targets achievable (this is what we want to verify/find)
AllTargetsProperty ==
    AllTargetsAchievable(pieces)

\* Combined validity: a valid solution satisfies all requirements
ValidSolution ==
    /\ TypeOK
    /\ PiecesPositive
    /\ PiecesSumToW
    /\ PiecesCanonical
    /\ AllTargetsProperty

\* Initial state: non-deterministically choose a partition
\* The model checker will explore all valid partitions
Init ==
    pieces \in Partitions

\* Next state: no transitions - this is a static problem
\* We use stuttering to allow the model checker to verify properties
Next ==
    UNCHANGED pieces

\* Specification
Spec == Init /\ [][Next]_pieces

\* Invariants to check (safety properties)
SafetyInvariants ==
    /\ TypeOK
    /\ PiecesPositive
    /\ PiecesSumToW
    /\ PiecesCanonical

\* The main property: if we find a valid partition, it must allow all targets
\* This is stated as: the current partition achieves all targets
CorrectnessProperty ==
    AllTargetsProperty

\* Alternative formulation: there exists a valid solution
\* (This is checked by seeing if Init is non-empty and satisfies AllTargetsProperty)
ExistsSolution ==
    \E p \in Partitions : AllTargetsAchievable(p)

===============================================================================