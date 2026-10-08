------------------------------- MODULE PlusCalExample -------------------------------
EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

Init == /\ x = 0
        /\ pc[ProcA] = "Start"
        /\ pc[ProcB] = "Start"

Next ==
    \/ /\ pc[ProcA] = "Start"
       /\ pc[ProcB] # "Done"
       /\ x' = x + 1
       /\ pc'[ProcA] = "Done"
       /\ pc'[ProcB] = pc[ProcB]
    \/ /\ pc[ProcB] = "Start"
       /\ pc[ProcA] # "Done"
       /\ x' = x + 1
       /\ pc'[ProcB] = "Done"
       /\ pc'[ProcA] = pc[ProcA]
    \/ /\ pc[ProcA] = "Done"
       /\ pc[ProcB] = "Done"
       /\ x' = x
       /\ pc'[ProcA] = pc[ProcA]
       /\ pc'[ProcB] = pc[ProcB]

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

Termination == <>[](pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

Invariant1 == x \in {0, 1, 2}

=============================================================================