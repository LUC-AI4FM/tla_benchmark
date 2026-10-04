---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Naturals

CONSTANTS Domain, InitValue

VARIABLES state

RECURSIVE RecFunc(_)

RecFunc(n) == 
    IF n <= 0 
    THEN 0
    ELSE n + RecFunc(n - 1)

FunctionRange == {RecFunc(d) : d \in Domain}

TypeOK == state \in Domain

Init == state = InitValue

Next == UNCHANGED state

Spec == Init /\ [][Next]_state

Invariant == state \in Domain /\ RecFunc(state) \in FunctionRange

=============================================================================