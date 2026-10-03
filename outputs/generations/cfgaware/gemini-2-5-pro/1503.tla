---- MODULE SmallStateMachine ----
EXTENDS Integers

VARIABLES x

IsGreaterThanOne(n) == n > 1

IsOdd(n, b) == IF b THEN n % 2 = 1 ELSE FALSE

Op(S, P(_), Q(_, _)) == {s \in S : P(s) /\ Q(s, TRUE)}

Init == x \in Op({1, 2, 3, 4, 5}, IsGreaterThanOne, IsOdd)

Next == UNCHANGED x

================================