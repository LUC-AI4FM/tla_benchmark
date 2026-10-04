---------------------------- MODULE balancescale ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

RECURSIVE Sum(_)
Sum(s) == IF s = <<>> THEN 0 ELSE Head(s) + Sum(Tail(s))

RECURSIVE OrderedPartitions(_, _)
OrderedPartitions(total, parts) ==
    IF parts = 1 THEN
        IF total >= 1 THEN {<<total>>} ELSE {}
    ELSE
        UNION {
            {<<w>> \o rest : rest \in OrderedPartitions(total - w, parts - 1)}
            : w \in 1..total - (parts - 1)
        }

RECURSIVE CanWeigh(_, _, _)
CanWeigh(target, weights, idx) ==
    IF idx > Len(weights) THEN
        target = 0
    ELSE
        \/ CanWeigh(target - weights[idx], weights, idx + 1)
        \/ CanWeigh(target, weights, idx + 1)
        \/ CanWeigh(target + weights[idx], weights, idx + 1)

CanWeighAll(weights) ==
    \A t \in 1..W : CanWeigh(t, weights, 1)

Solutions == {p \in OrderedPartitions(W, N) : CanWeighAll(p)}

SolutionExists == Solutions /= {}

FindSolution ==
    IF SolutionExists THEN
        CHOOSE p \in Solutions : TRUE
    ELSE
        <<>>

CheckResult ==
    IF SolutionExists THEN
        PrintT(<<"Solution found:", FindSolution>>)
    ELSE
        PrintT("No solution exists")

ASSUME CheckResult

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_dummy

=============================================================================