MODULE SmallSM

EXTENDS Naturals, TLC

CONSTANTS Domain

VARIABLES x, y

Init == /\ x \in 1..5
        /\ y = [i \in 1..5 |-> 0]

Foo(x, f) == IF x = 1 THEN f[x |-> 42] ELSE f

Next == /\ x' = x
        /\ y' = Foo(x, y)

Spec == Init /\ [] ( Next )_ <<x, y>>