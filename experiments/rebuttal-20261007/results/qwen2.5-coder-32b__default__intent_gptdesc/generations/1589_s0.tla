------------------------------- MODULE EuclideanGCD -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxInt \* Assume MaxInt is the upper bound for model checking

VARIABLES x, y

Init == /\ x \in 1..MaxInt
        /\ y \in 1..MaxInt

Next ==
    \/ /\ x > y
       /\ x' = x - y
       /\ y' = y
    \/ /\ y > x
       /\ x' = x
       /\ y' = y - x
    \/ /\ x = y
       /\ x' = 0
       /\ y' = 0

Spec ==
    /\ Init
    /\ [][Next]_<<x, y>>
    /\ <</\WF_vars(Next)>>_<<x, y>>

Invariants ==
    /\ \/ x > 0 /\ y > 0
       \/ x = 0 /\ y > 0
       \/ x > 0 /\ y = 0
    /\ GCD(x', y') = GCD(x, y)

GCD(a, b) == CHOOSE d \in 1..MaxInt : /\ d \leq a
                                         /\ d \leq b
                                         /\ \A k \in 1..MaxInt : (k > d => (\lnot (k \leq a /\ k \leq b)))

Termination ==
    <>[]<>(x = 0 \/ y = 0)

FunctionalCorrectness ==
    [](x = 0 => GCD(x, y) = y)
    /\ [](y = 0 => GCD(x, y) = x)

Liveness ==
    Termination

=============================================================================