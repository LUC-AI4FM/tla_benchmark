------------------------------ MODULE RecFuncDemo ------------------------------
EXTENDS Naturals

CONSTANTS Domain, InitVal

VARIABLE x

RECURSIVE fib
fib == [n \in Domain |-> IF n = 0 THEN 0
                      ELSE IF n = 1 THEN 1
                      ELSE fib[n-1] + fib[n-2]]

Init == x = InitVal /\ InitVal \in {fib(n) : n \in Domain}

Next == UNCHANGED <<x>>

Spec == Init /\ [][Next]_<<x>>

Inv == x \in {fib(n) : n \in Domain}

THEOREM InvHolds == Spec => []Inv
=============================================================================