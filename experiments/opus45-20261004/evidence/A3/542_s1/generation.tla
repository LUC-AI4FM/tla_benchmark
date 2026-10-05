-------------------------------- MODULE PlusCalIncrement --------------------------------
EXTENDS Integers, TLC

CONSTANT ProcSet

VARIABLES x, pc

vars == << x, pc >>

ProcA == "ProcA"
ProcB == "ProcB"

Init == 
    /\ x = 0
    /\ pc = [p \in {ProcA, ProcB} |-> "a1"]

ProcAAction ==
    /\ pc[ProcA] = "a1"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcA] = "Done"]

ProcBAction ==
    /\ pc[ProcB] = "a1"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcB] = "Done"]

Terminating ==
    /\ pc[ProcA] = "Done"
    /\ pc[ProcB] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ProcAAction
    \/ ProcBAction
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariant: x is always between 0 and 2
TypeInvariant ==
    /\ x \in 0..2
    /\ pc[ProcA] \in {"a1", "Done"}
    /\ pc[ProcB] \in {"a1", "Done"}

\* Safety invariant: when both processes are done, x equals 2
FinalValueCorrect ==
    (pc[ProcA] = "Done" /\ pc[ProcB] = "Done") => x = 2

\* Liveness property: eventually all processes terminate
Termination == <>(pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

=============================================================================