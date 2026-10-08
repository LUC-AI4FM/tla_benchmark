MODULE SimpleAssertion
EXTENDS Naturals

VARIABLES x, terminated

Init ==
    /\ x \in 1..10
    /\ terminated = FALSE

AssertAction ==
    /\ terminated = FALSE
    /\ x^2 <= 100
    /\ terminated' = TRUE
    /\ x' = x

Stutter ==
    /\ terminated
    /\ x' = x
    /\ terminated' = terminated

Next == AssertAction \/ Stutter

vars == <<x, terminated>>

Spec == Init /\ [][Next]_vars

Safety == [] (x^2 <= 100)

Termination == <> terminated