---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

vars == <<x, pc>>

ProcSet == {ProcA, ProcB}

Init == 
    /\ x = 0
    /\ pc = [p \in ProcSet |-> "start"]

procA == 
    /\ pc[ProcA] = "start"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcA] = "Done"]

procB == 
    /\ pc[ProcB] = "start"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcB] = "Done"]

Terminating ==
    /\ \A p \in ProcSet : pc[p] = "Done"
    /\ UNCHANGED vars

Next == 
    \/ procA
    \/ procB
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(\A p \in ProcSet : pc[p] = "Done")

TypeOK ==
    /\ x \in Int
    /\ pc \in [ProcSet -> {"start", "Done"}]

=========================================================================