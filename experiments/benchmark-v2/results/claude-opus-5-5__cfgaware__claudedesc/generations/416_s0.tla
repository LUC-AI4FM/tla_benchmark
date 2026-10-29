------------------------------ MODULE PrimeTest ------------------------------
EXTENDS Integers, TLC

VARIABLES x, y

vars == <<x, y>>

Action1(c, d) == c' = [c EXCEPT ![1] = d']

Action2(c, d) == c' = [c EXCEPT ![1] = d]

Init ==
    /\ x = [i \in {1, 2} |-> i]
    /\ y = 1

Next ==
    \/ /\ y = 1
       /\ y' = 2
       /\ Action1(x, y)
       /\ IF x'[1] = 2
            THEN Print("Test 1 OK", TRUE)
            ELSE Assert(FALSE, "Test 1 Failed")
    \/ /\ y = 1
       /\ y' = 2
       /\ Action2(x, y)
       /\ IF x'[1] = 1
            THEN Print("Test 2 OK", TRUE)
            ELSE Assert(FALSE, "Test 2 Failed")
    \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars

Inv == TRUE

Constraint == TRUE

=============================================================================