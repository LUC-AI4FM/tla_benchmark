------------------------------- MODULE SmallStateMachine -----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    XDomain == {1, 2, 3, 4, 5}

VARIABLES 
    x, y

Init == /\ x \in XDomain
        /\ y = [XDomain -> 0]

Foo(y, x) == IF x = 1 THEN [y EXCEPT ![x] = 42] ELSE y

Next == \/ /\ UNCHANGED x
            /\ y' = Foo(y, x)

Spec == Init /\ [][Next]_<<x, y>>

=============================================================================