MODULE BalanceScalePuzzle
EXTENDS Naturals, Sequences

CONSTANTS W, N

VARIABLE solution

(* Helper definitions *)

NonDecr(s) ==
    \A i \in 1..N-1 : s[i] <= s[i+1]

SumProduct(c,s) ==
    Sum(\lambda i \in 1..N : c[i]*s[i])

SolutionSet ==
    { s \in [i \in 1..N -> Nat] :
        \A i \in 1..N : 1 <= s[i]
        /\ NonDecr(s)
        /\ Sum(\lambda i \in 1..N : s[i]) = W }

ValidPartition(s) ==
    \A k \in 1..W :
        EXISTS c \in [i \in 1..N -> {-1,0,1}] :
            SumProduct(c,s) = k

ExistsValid == EXISTS s \in SolutionSet : ValidPartition(s)

NoSolution == "No solution"

Init ==
    IF ExistsValid THEN
        solution \in { s \in SolutionSet : ValidPartition(s) }
    ELSE
        solution = NoSolution

Spec == Init

===============================================================================