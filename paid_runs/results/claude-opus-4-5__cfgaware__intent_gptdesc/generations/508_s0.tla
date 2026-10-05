---------------------------- MODULE Specification ----------------------------

VARIABLES x, pc

vars == <<x, pc>>

TypeOK == x \in 1..10 /\ pc \in {"init", "assert", "done"}

Init == 
    /\ x \in 1..10
    /\ pc = "init"

AssertAction ==
    /\ pc = "init"
    /\ x * x <= 100
    /\ pc' = "assert"
    /\ x' = x

Terminate ==
    /\ pc = "assert"
    /\ pc' = "done"
    /\ x' = x

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ AssertAction
    \/ Terminate
    \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(AssertAction) /\ WF_vars(Terminate)

Safety == x * x <= 100

Termination == <>(pc = "done")

=============================================================================