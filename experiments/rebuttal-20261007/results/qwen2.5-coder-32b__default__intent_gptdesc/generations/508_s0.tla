------------------------------- MODULE SimpleProgram -------------------------------
EXTENDS Integers, TLC

CONSTANTS InitValue \* Unused in this specification but included as per requirements

VARIABLES x, terminated

Init == /\ x \in 1..10
        /\ terminated = FALSE

Next ==
    \/ /\ \neg terminated
       /\ x * x <= 100
       /\ 'x' = x
       /\ 'terminated' = TRUE
    \/ /\ terminated
       /\ UNCHANGED <<x, terminated>>

Spec == /\ Init
        /\ [][Next]_<<x, terminated>>
        /\ WF_next(<<x, terminated>>)

\* Safety properties
AssertedBound == \A s \in StateSpace: s.terminated => s.x * s.x <= 100

\* Liveness property
Termination == <>(terminated = TRUE)

StateSpace == { <<s.x, s.terminated>> : s \in [x \in 1..10, terminated \in BOOLEAN] }

=============================================================================