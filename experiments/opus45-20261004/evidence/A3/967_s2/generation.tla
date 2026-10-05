---------------------------- MODULE StoneCutting ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

RECURSIVE Sum(_)
Sum(s) == IF s = <<>> THEN 0 ELSE Head(s) + Sum(Tail(s))

RECURSIVE OrderedPartitions(_, _)
OrderedPartitions(total, parts) ==
    IF parts = 0 THEN
        IF total = 0 THEN {<<>>} ELSE {}
    ELSE IF parts = 1 THEN
        IF total >= 1 THEN {<<total>>} ELSE {}
    ELSE
        UNION {
            {<<k>> \o rest : rest \in OrderedPartitions(total - k, parts - 1)}
            : k \in 1..total - (parts - 1)
        }

AllPartitions == OrderedPartitions(W, N)

Coefficients == {-1, 0, 1}

AllCoeffVectors == [1..N -> Coefficients]

CanWeigh(weights, target) ==
    \E coeffs \in AllCoeffVectors :
        Sum([i \in 1..N |-> coeffs[i] * weights[i]]) = target

IsSolution(weights) ==
    \A target \in 1..W : CanWeigh(weights, target)

Solutions == {weights \in AllPartitions : IsSolution(weights)}

HasSolution == Solutions /= {}

ASSUME
    IF HasSolution THEN
        PrintT(<<"Solution found:", CHOOSE s \in Solutions : TRUE>>)
    ELSE
        PrintT("No solution exists")

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_dummy

SolutionExists == HasSolution

=============================================================================