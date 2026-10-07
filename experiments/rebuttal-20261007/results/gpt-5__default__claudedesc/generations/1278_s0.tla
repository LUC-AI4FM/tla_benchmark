---- MODULE EvenEven0To9 ----
EXTENDS Integers

CONSTANTS UnusedConst \* Unused; present to satisfy the requested section.

VARIABLES s

F(x) == /\ x \in 0..9
        /\ x % 2 = 0

Init == s = 0

Next == F(s')

Spec == Init /\ [] [Next]_s
====