---------------------------- MODULE SimpleAssertion ----------------------------
EXTENDS Integers, TLC

VARIABLES pc, chosen

vars == <<pc, chosen>>

Init ==
    /\ chosen \in 1..10
    /\ pc = "check"

Check ==
    /\ pc = "check"
    /\ Assert(chosen * chosen <= 100, "Square exceeds 100")
    /\ pc' = "done"
    /\ UNCHANGED chosen

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Check
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInvariant ==
    /\ chosen \in 1..10
    /\ pc \in {"check", "done"}

SquarePropertyInvariant ==
    chosen * chosen <= 100

Termination ==
    <>(pc = "done")

================================================================================