------------------------------- MODULE SimpleConcurrentProgram -------------------------------
EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

Init == /\ x = 0
        /\ pc[ProcA] = "Start"
        /\ pc[ProcB] = "Start"

Next ==
    \/ /\ pc[ProcA] = "Start"
       /\ pc[ProcB] \in {"Start", "Done"}
       /\ x' = x + 1
       /\ pc'[ProcA] = "Done"
       /\ pc'[ProcB] = pc[ProcB]
    \/ /\ pc[ProcB] = "Start"
       /\ pc[ProcA] \in {"Start", "Done"}
       /\ x' = x + 1
       /\ pc'[ProcB] = "Done"
       /\ pc'[ProcA] = pc[ProcA]
    \/ /\ pc[ProcA] = "Done"
       /\ pc[ProcB] = "Done"
       /\ UNCHANGED <<x, pc>>

Spec ==
    /\ Init
    /\ [][Next]_<<pc[ProcA], pc[ProcB]>>
    /\ WF_[Next]_<<pc[ProcA], pc[ProcB]>>

Termination == <>[](pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

=============================================================================