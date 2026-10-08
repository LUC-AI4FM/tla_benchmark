------------------------------- MODULE SmallStateMachine -------------------------------

EXTENDS Integers, Functions

CONSTANTS 
    Domain \in SUBSET {1..5}

VARIABLES 
    x, y

Init == /\ x \in {1..5}
        /\ y = [Domain -> 0]

Foo(x, y) ==
    IF x = 1 THEN
        [y EXCEPT ![x] = 42]
    ELSE
        y

Next == /\ UNCHANGED x
          /\ y' = Foo(x, y)

Spec == Init /\ [][Next]_<<x,y>>

=============================================================================