------------------------------- MODULE PrimeArgs -------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = [i \in {1, 2} |-> i]
    /\ y = 1

\* Updates the first argument using the PRIMED value of the second argument
Action1(c, d) == c' = [c EXCEPT ![1] = d']

\* Updates the first argument using the UNPRIMED (current) value of the second argument
Action2(c, d) == c' = [c EXCEPT ![1] = d]

TypeOK ==
    /\ x \in [{1, 2} -> Int]
    /\ y \in Int

Next ==
    \/ /\ y = 1
       /\ y' = 2
       /\ Action1(x, y)
       /\ PrintT("Testing Action1 (primed argument)")
       /\ IF x'[1] = 2
            THEN PrintT("Test 1 OK")
            ELSE PrintT("Test 1 FAILED")
       /\ Assert(x'[1] = 2, "Test 1 failed: x'[1] should equal 2")
    \/ /\ y = 1
       /\ y' = 2
       /\ Action2(x, y)
       /\ PrintT("Testing Action2 (unprimed argument)")
       /\ IF x'[1] = 1
            THEN PrintT("Test 2 OK")
            ELSE PrintT("Test 2 FAILED")
       /\ Assert(x'[1] = 1, "Test 2 failed: x'[1] should equal 1")
    \/ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_vars

Invariant == TRUE

Constraint == TRUE

=============================================================================