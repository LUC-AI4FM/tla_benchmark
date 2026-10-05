---------------------------- MODULE J ----------------------------
EXTENDS Integers

VARIABLES x, y

S == {1, 2, 3, 4, 5}

Foo(f) == IF x = 1 THEN [f EXCEPT ![x] = 42] ELSE f

Init == /\ x \in S
        /\ y = [i \in S |-> 0]

Next == /\ x' = x
        /\ y' = Foo(y)

Spec == Init /\ [][Next]_<<x, y>>

=================================================================