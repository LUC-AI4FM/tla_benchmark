------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    XDomain == {1, 2, 3, 4, 5}

VARIABLES 
    x,
    y

Init == /\ x \in XDomain
        /\ y = [d \in XDomain |-> 0]

Foo(x, y) == 
    IF x = 1 THEN
        [y EXCEPT ![x] = 42]
    ELSE
        y

Next == /\ UNCHANGED x
        /\ y' = Foo(x, y)

Spec == Init /\ [][Next]_<<x, y>>

================================================================================