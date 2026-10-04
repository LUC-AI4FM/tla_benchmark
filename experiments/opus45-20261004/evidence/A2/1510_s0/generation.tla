---------------------------- MODULE J ----------------------------
EXTENDS Integers

CONSTANTS S

VARIABLES x, y

Foo(f, v) == IF v = 1 THEN [f EXCEPT ![v] = 42] ELSE f

Init == 
    /\ x \in S
    /\ y = [i \in S |-> 0]

Next == 
    /\ x' = x
    /\ y' = Foo(y, x)

Spec == Init /\ [][Next]_<<x, y>>

=================================================================