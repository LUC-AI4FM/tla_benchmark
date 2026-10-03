---------------------------- MODULE balancescale ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS W, N

RECURSIVE SeqSum(_)
SeqSum(s) ==
    IF s = << >> THEN 0
    ELSE Head(s) + SeqSum(Tail(s))

RECURSIVE Partitions(_, _)
Partitions(total, parts) ==
    IF parts = 1 THEN
        IF total >= 1 THEN {<<total>>} ELSE {}
    ELSE
        UNION {
            {<<i>> \o p : p \in Partitions(total - i, parts - 1)}
            : i \in 1..total - (parts - 1)
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

Solutions == {p \in Partitions(W, N) : CanWeighAll(p)}

SolutionExists == Solutions /= {}

PrintSolution ==
    IF SolutionExists THEN
        PrintT(<<"Solution found:", CHOOSE s \in Solutions : TRUE>>)
    ELSE
        PrintT("No solution exists")

ASSUME PrintSolution

=============================================================================