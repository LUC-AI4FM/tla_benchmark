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
            {<<w>> \o rest : rest \in OrderedPartitions(total - w, parts - 1)}
            : w \in 1..total - (parts - 1)
        }

Coefficients == {-1, 0, 1}

CoeffSeqs(n) ==
    IF n = 0 THEN {<<>>}
    ELSE {<<c>> \o rest : c \in Coefficients, rest \in CoeffSeqs(n - 1)}

RECURSIVE DotProduct(_, _)
DotProduct(weights, coeffs) ==
    IF weights = <<>> THEN 0
    ELSE Head(weights) * Head(coeffs) + DotProduct(Tail(weights), Tail(coeffs))

CanWeigh(weights, target) ==
    \E coeffs \in CoeffSeqs(Len(weights)) :
        DotProduct(weights, coeffs) = target

IsSolution(weights) ==
    /\ Len(weights) = N
    /\ Sum(weights) = W
    /\ \A t \in 1..W : CanWeigh(weights, t)

AllPartitions == OrderedPartitions(W, N)

Solutions == {p \in AllPartitions : IsSolution(p)}

ASSUME
    LET sols == Solutions
    IN IF sols # {} THEN
           PrintT(<<"Solution found:", CHOOSE s \in sols : TRUE>>)
       ELSE
           PrintT("No solution exists")

VARIABLE dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_dummy

SolutionExists == Solutions # {}

TypeInvariant == dummy \in {0}

=============================================================================