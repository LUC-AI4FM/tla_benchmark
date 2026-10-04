---------------------------- MODULE StoneCutting ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

RECURSIVE Sum(_)
Sum(seq) ==
    IF seq = << >>
    THEN 0
    ELSE Head(seq) + Sum(Tail(seq))

RECURSIVE OrderedPartitions(_, _)
OrderedPartitions(total, parts) ==
    IF parts = 0
    THEN IF total = 0 THEN {<< >>} ELSE {}
    ELSE IF parts = 1
    THEN IF total >= 1 THEN {<<total>>} ELSE {}
    ELSE LET maxFirst == total - parts + 1
         IN UNION {
             {<<w>> \o rest : rest \in OrderedPartitions(total - w, parts - 1)}
             : w \in 1..maxFirst
         }

Coefficients == {-1, 0, 1}

AllCoeffSeqs(n) ==
    IF n = 0
    THEN {<< >>}
    ELSE {<<c>> \o rest : c \in Coefficients, rest \in AllCoeffSeqs(n - 1)}

RECURSIVE DotProduct(_, _)
DotProduct(seq1, seq2) ==
    IF seq1 = << >> \/ seq2 = << >>
    THEN 0
    ELSE (Head(seq1) * Head(seq2)) + DotProduct(Tail(seq1), Tail(seq2))

CanWeigh(weights, target) ==
    \E coeffs \in AllCoeffSeqs(Len(weights)) :
        DotProduct(coeffs, weights) = target

IsSolution(weights) ==
    /\ Len(weights) = N
    /\ Sum(weights) = W
    /\ \A target \in 1..W : CanWeigh(weights, target)

Solutions == {weights \in OrderedPartitions(W, N) : IsSolution(weights)}

SolutionExists == Solutions /= {}

ASSUME
    IF SolutionExists
    THEN PrintT(<<"Solution found:", CHOOSE sol \in Solutions : TRUE>>)
    ELSE PrintT("No solution exists")

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_dummy

TypeInvariant == dummy = 0

SolutionInvariant ==
    \A sol \in Solutions :
        /\ Len(sol) = N
        /\ Sum(sol) = W
        /\ \A t \in 1..W : CanWeigh(sol, t)

=============================================================================