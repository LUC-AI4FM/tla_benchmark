---------------------------- MODULE WeighingPieces ----------------------------

CONSTANTS W, N

ASSUME WPositive == W \in Nat /\ W > 0
ASSUME NPositive == N \in Nat /\ N > 0

VARIABLES pieces

\* All possible multisets of N positive integers that sum to W
\* Represented as sequences sorted in non-decreasing order to avoid duplicates
Partitions == { p \in [1..N -> 1..W] : 
                /\ \A i \in 1..(N-1) : p[i] <= p[i+1]  \* sorted (non-decreasing)
                /\ LET Sum == CHOOSE f : f = [s \in 0..N |-> IF s = 0 THEN 0 
                                                             ELSE f[s-1] + p[s]]
                   IN Sum[N] = W }

\* Helper: compute sum of elements in a function over 1..N
SumPieces(p) == LET RECURSIVE SumRec(_)
                    SumRec(i) == IF i = 0 THEN 0 ELSE p[i] + SumRec(i-1)
                IN SumRec(N)

\* More direct definition of valid partitions
ValidPartitions == { p \in [1..N -> 1..W] : 
                     /\ \A i \in 1..(N-1) : p[i] <= p[i+1]
                     /\ SumPieces(p) = W }

\* Coefficients: -1 means right pan, 0 means unused, 1 means left pan
Coefficients == [1..N -> {-1, 0, 1}]

\* Compute the net weight difference achieved by a coefficient assignment
\* Positive result means left pan is heavier by that amount
NetWeight(p, c) == LET RECURSIVE NetRec(_)
                      NetRec(i) == IF i = 0 THEN 0 ELSE c[i] * p[i] + NetRec(i-1)
                  IN NetRec(N)

\* Check if target t can be achieved: there exists coefficients c such that
\* the left pan minus right pan equals t (left pan has extra weight t)
CanAchieve(p, t) == \E c \in Coefficients : NetWeight(p, c) = t

\* Property: All targets from 1 to W can be achieved
AllTargetsAchievable(p) == \A t \in 1..W : CanAchieve(p, t)

\* Type invariant: pieces must be positive integers
PiecesPositive == \A i \in 1..N : pieces[i] \in Nat /\ pieces[i] > 0

\* Invariant: pieces sum to W
PiecesSumToW == SumPieces(pieces) = W

\* Invariant: pieces form a valid multiset (sorted to eliminate duplicates)
PiecesSorted == \A i \in 1..(N-1) : pieces[i] <= pieces[i+1]

\* Combined type invariant
TypeInvariant == /\ pieces \in [1..N -> 1..W]
                 /\ PiecesPositive
                 /\ PiecesSorted
                 /\ PiecesSumToW

\* The main property: all targets can be balanced
Balanceable == AllTargetsAchievable(pieces)

\* Initial state: non-deterministically choose a valid partition
Init == pieces \in ValidPartitions

\* No transitions - this is a static constraint satisfaction problem
Next == UNCHANGED pieces

\* The specification
Spec == Init /\ [][Next]_pieces

\* Invariant combining all requirements
ValidSolution == TypeInvariant /\ Balanceable

\* Property to check: if we find any state, it should be a valid solution
\* If no valid partition exists, Init will be empty and model checking reports this
CorrectPartition == Balanceable

=============================================================================