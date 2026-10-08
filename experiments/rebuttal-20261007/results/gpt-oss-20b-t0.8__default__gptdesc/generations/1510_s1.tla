MODULE SmallSM
EXTENDS Integers

VARIABLES x, y

Foo(x, f) ==
    IF x = 1
    THEN [i \in 1..5 |-> IF i = x THEN 42 ELSE f[i]]
    ELSE f

Init ==
    /\ x ∈ 1..5
    /\ y = [i \in 1..5 |-> 0]

Next ==
    /\ x' = x
    /\ y' = Foo(x, y)

Spec == Init /\ [][Next]_<<x,y>>