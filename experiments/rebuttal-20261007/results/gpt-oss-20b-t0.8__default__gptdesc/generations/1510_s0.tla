MODULE SmallStateMachine
EXTENDS Naturals

VARIABLES x, y

SetX == {1,2,3,4,5}

Foo(idx, f) ==
    IF idx = 1
        THEN [i \in SetX |-> IF i = idx THEN 42 ELSE f[i]]
        ELSE f

Init ==
    /\ x \in SetX
    /\ y = [i \in SetX |-> 0]

Next ==
    /\ x' = x
    /\ y' = Foo(x, y)

Spec == Init /\ [] Next