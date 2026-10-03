---- MODULE small_algorithm ----
EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x \in 1..10
    /\ pc = "start"

A ==
    /\ pc = "start"
    /\ Assert(x^2 <= 100, "Assertion failed: x^2 <= 100")
    /\ pc' = "Done"
    /\ x' = x

Next == A

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Invariant == x^2 <= 100

Termination == <>(pc = "Done")

=============================================================================