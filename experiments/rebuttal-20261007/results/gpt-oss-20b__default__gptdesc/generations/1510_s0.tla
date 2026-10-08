MODULE SmallSM
EXTENDS Naturals

VARIABLES x, y

Init == /\ x \in 1..5
        /\ y = [i \in 1..5 |-> 0]

Foo(x, y) ==
    IF x = 1 THEN [y EXCEPT ![x] = 42]
    ELSE y

Next == /\ x' = x
          /\ y' = Foo(x, y)

Spec == Init /\ [] Next

===============================================================================