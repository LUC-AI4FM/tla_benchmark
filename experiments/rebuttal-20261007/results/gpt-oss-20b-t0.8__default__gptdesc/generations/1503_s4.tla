MODULE SmallSM
EXTENDS Integers

VARIABLE x

Op == \lambda S, P, Q . { s \in S : P(s) /\ Q(s, TRUE) }

IsGreaterThanOne(s) == (s > 1)

OddTrue(s, b) == (b /\ Odd(s))

Init == x \in Op({1,2,3,4,5}, IsGreaterThanOne, OddTrue)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
