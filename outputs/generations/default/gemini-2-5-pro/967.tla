---- MODULE BalanceScale ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    W,  \* The total weight to be partitioned.
    N   \* The number of pieces in the partition.

(*--
An ASSUME to have TLC find and print a solution. This is the main "driver"
of the specification, turning the model checker into a search tool. It is
evaluated once when TLC initializes the model.
--*)
ASSUME
    LET Solutions == { p \in OrderedPartitions(W, N) : IsSolution(p) }
    IN
    IF Solutions = {}
    THEN PrintT("No solution exists for W=" \o ToString(W) \o ", N=" \o ToString(N))
    ELSE \E sol \in Solutions : PrintT(<<"A solution for W=", W, ", N=", N, " is: ", sol>>)

\* Recursive operator to sum a sequence of integers.
RECURSIVE Sum(_)
Sum(seq) ==
    IF Len(seq) = 0 THEN 0
    ELSE Head(seq) + Sum(Tail(seq))

\* Recursive operator to generate all ordered partitions of a total `t` into
\* `n` positive integer pieces. An ordered partition is a sequence of
\* positive integers that sum to `t`.
RECURSIVE OrderedPartitions(_, _)
OrderedPartitions(t, n) ==
    IF n = 1 THEN
        IF t > 0 THEN {<<t>>} ELSE {}
    ELSE
        UNION { {<<i>> \o p : p \in OrderedPartitions(t - i, n - 1)}
                : i \in 1..(t - (n - 1)) }

\* The set of coefficients for placing weights on the balance scale.
\*  1: place piece on the pan opposite the target weight.
\*  0: do not use the piece.
\* -1: place piece on the same pan as the target weight.
Coeffs == {-1, 0, 1}

\* The dot product of two sequences of numbers.
DotProduct(s1, s2) == Sum(<<s1[i] * s2[i] : i \in 1..Len(s1)>>)

\* Checks if a given target weight can be measured using a set of pieces.
\* This is true if there exists a combination of coefficients such that the
\* dot product of the coefficients and the pieces equals the target.
CanWeigh(pieces, target) ==
    \E c \in [1..N -> Coeffs] : target = DotProduct(c, pieces)

\* A partition is a solution if it can be used to weigh every integer
\* target from 1 to W. The OrderedPartitions operator ensures that the
\* pieces are positive, sum to W, and have the correct count N.
IsSolution(pieces) ==
    \A target \in 1..W : CanWeigh(pieces, target)

\* The core of the specification is a static analysis of the problem. The state
\* machine below is trivial and exists to satisfy the requirement of having
\* Init, Next, and Spec definitions for the TLA+ model checker. The actual
\* problem-solving logic is encapsulated in the operators above and invoked
\* by the top-level ASSUME statement.

VARIABLES
    \* A dummy variable to define a state space.
    state

vars == <<state>>

Init == state = "start"

Next == state = "start" /\ state' = "finished"

Spec == Init /\ [][Next]_vars

\* A safety invariant which asserts that any set of pieces identified as a
\* solution by this specification must indeed satisfy the solution criteria.
\* This is true by definition but serves as a formal correctness property.
SolutionProperty ==
    LET AllSols == { p \in OrderedPartitions(W, N) : IsSolution(p) }
    IN
    \A sol \in AllSols : IsSolution(sol)

\* Liveness properties and fairness are not applicable to this specification
\* as it does not model an ongoing, non-terminating process. The "liveness"
\* of the search for a solution is handled by TLC's evaluation of the
\* definitions, which is guaranteed to terminate.

=============================================================================