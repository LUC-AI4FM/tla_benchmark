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

RECURSIVE Coefficients(_)
Coefficients(n) ==
    IF n = 0 THEN {<<>>}
    ELSE {<<c>> \o rest : c \in {-1, 0, 1}, rest \in Coefficients(n - 1)}

RECURSIVE DotProduct(_, _)
DotProduct(s1, s2) ==
    IF s1 = <<>> THEN 0
    ELSE Head(s1) * Head(s2) + DotProduct(Tail(s1), Tail(s2))

CanWeigh(weights, target) ==
    \E coeffs \in Coefficients(Len(weights)) :
        DotProduct(coeffs, weights) = target

IsSolution(weights) ==
    /\ Len(weights) = N
    /\ Sum(weights) = W
    /\ \A t \in 1..W : CanWeigh(weights, t)

AllPartitions == OrderedPartitions(W, N)

Solutions == {p \in AllPartitions : IsSolution(p)}

ASSUME
    LET sols == Solutions
    IN IF sols = {} THEN
           PrintT(<<"No solution exists for W =", W, "N =", N>>)
       ELSE
           PrintT(<<"Solution found:", CHOOSE s \in sols : TRUE>>)

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_dummy

TypeInvariant == dummy = 0

SolutionExists == Solutions /= {}

=============================================================================