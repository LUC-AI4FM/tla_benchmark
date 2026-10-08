------------------------------- MODULE RecursiveFunctionExample -------------------------------

CONSTANTS Domain, InitialValue

VARIABLES state

DOMAIN Domain == {0, 1, 2, 3, 4}

RecursiveFunction(n) ==
    IF n = 0 THEN 0
    ELSE RecursiveFunction(n - 1) + 1

Init == state = InitialValue

Next == TRUE \* The state never changes

Spec == Init /\ [][Next]_<<state>>

Invariants ==
    /\ state \in Domain
    /\ \E n \in Domain : state = RecursiveFunction(n)

THEOREM Spec => [] Invariants

=============================================================================