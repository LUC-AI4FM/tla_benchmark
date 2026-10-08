```
MODULE CyclicCounter
EXTENDS Integers

CONSTANTS None

VARIABLES state

Init == state = 0

Next == state' = (state + 1) % 3

Spec == Init /\ [][Next]_state

StateInvariant == state \in {0, 1, 2}

Determinism == \A s \in {0, 1, 2} : 
                \E t \in {0, 1, 2} : (s = 0 /\ t = 1) \/ 
                                         (s = 1 /\ t = 2) \/ 
                                         (s = 2 /\ t = 0)

Reachability1 == <> (state = 1)
Reachability2 == <> (state = 2)

WrapAround == <>(state = 2 /\ state' = 0)

CycleLiveness == []<> (state = 0) /\ []<> (state = 1) /\ []<> (state = 2)

THEOREM Spec => []StateInvariant
THEOREM Spec => Determinism
THEOREM Spec => Reachability1
THEOREM Spec => Reachability2
THEOREM Spec => WrapAround
THEOREM Spec => CycleLiveness

=============================================================================
```
Note: The `None` in the `CONSTANTS None` line is used because TLA+ requires at least one constant to be declared, even if no constants are actually used. Similarly, the `EXTENDS Integers` line is used to allow the use of integer arithmetic operations like `%`.