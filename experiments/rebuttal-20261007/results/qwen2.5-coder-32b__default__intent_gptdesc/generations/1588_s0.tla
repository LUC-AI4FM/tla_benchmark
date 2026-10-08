------------------------------- MODULE EuclideanGCD -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS A, N \* A is a fixed positive integer, N is the upper bound for B

VARIABLES x, y, initialB

Init == /\ x = A
        /\ y \in 1..N
        /\ initialB = y

Next ==
    \/ /\ x < y
       /\ x' = y
       /\ y' = x
       /\ initialB' = initialB
    \/ /\ x >= y
       /\ x' = x - y
       /\ y' = y
       /\ initialB' = initialB

Spec == Init /\ [][Next]_<<x, y>>

\* Safety: all intermediate values remain natural numbers within appropriate bounds and never become zero unexpectedly except as permitted by the algorithm's rules.
Safety ==
    \/ x > 0
    \/ y > 0

\* Invariant: a nontrivial invariant capturing that at every step the set of common divisors of the two numbers is unchanged (i.e., the GCD of the pair remains equal to the GCD of A and the initial B).
GcdInvariant ==
    Gcd({x, y}) = Gcd({A, initialB})

\* Liveness: eventual termination—under weak fairness of the loop steps, the algorithm reaches a halting state where one component is zero.
Termination ==
    <>(x = 0 \/ y = 0)

\* Correctness at termination: when the algorithm halts, the nonzero component equals gcd(A, initial B).
Correctness ==
    [](x' = 0 -> y' = Gcd({A, initialB}))
    /\ [](y' = 0 -> x' = Gcd({A, initialB}))

\* Fairness condition
WF == WF_next(<<x, y>>)

THEOREM Spec => []Safety
THEOREM Spec => []GcdInvariant
THEOREM Spec /\ WF => Termination
THEOREM Spec /\ WF => Correctness

=============================================================================