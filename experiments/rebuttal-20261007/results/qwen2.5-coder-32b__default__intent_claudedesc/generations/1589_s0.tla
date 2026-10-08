------------------------------- MODULE EuclidGCD -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxValue \* Assume MaxValue is 20 for this problem

VARIABLES x, y

Init == /\ x \in 1..MaxValue
        /\ y \in 1..MaxValue

Next ==
    \/ /\ x > y
       /\ x' = x - y
       /\ y' = y
    \/ /\ x <= y
       /\ x' = y
       /\ y' = x

Spec == Init /\ [][Next]_<<x, y>>

Termination == <>(x = 0)

GCD(a, b) ==
    LET Recur(a, b) ==
        IF a = 0 THEN b
        ELSE IF b = 0 THEN a
        ELSE IF a >= b THEN Recur(a - b, b)
        ELSE Recur(a, b - a)
    IN Recur(a, b)

Correctness == [](x = 0 => y = GCD(x', y'))

Invariants ==
    /\ Correctness

Liveness ==
    \/ Termination

Fairness ==
    WF_next(<<x, y>>)

THEOREM Spec => []Invariants
THEOREM Spec => <>Liveness
=============================================================================