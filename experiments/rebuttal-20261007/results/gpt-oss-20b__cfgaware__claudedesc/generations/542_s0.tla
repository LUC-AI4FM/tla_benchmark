---- MODULE SimpleIncrement ----
EXTENDS Naturals

CONSTANTS ProcA, ProcB
Processes == {ProcA, ProcB}

VARIABLE x, pc

Init ==
    /\ x = 0
    /\ pc = [p \in Processes |-> "Start"]

a ==
    /\ pc[ProcA] = "Start"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcA] = "Done"]

b ==
    /\ pc[ProcB] = "Start"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcB] = "Done"]

Terminating ==
    /\ pc[ProcA] = "Done"
    /\ pc[ProcB] = "Done"
    /\ x' = x
    /\ pc' = pc

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_<<x, pc>>

Termination ==
    /\ []<>(pc[ProcA] = "Done")
    /\ []<>(pc[ProcB] = "Done")

====