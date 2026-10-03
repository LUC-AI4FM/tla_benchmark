------------------------------- MODULE SmallStateMachine -------------------------------

CONSTANTS
    x \in {1..5}

VARIABLES
    y

Init == /\ y = [i \in {1,2,3,4,5} |-> 0]
        /\ x \in {1..5}

Foo(y, x) ==
    IF x = 1 THEN [y EXCEPT ![x] = 42]
    ELSE y

Next == /\ y' = Foo(y, x)
          /\ x' = x

Spec == Init /\ [][Next]_<<x,y>>

=============================================================================