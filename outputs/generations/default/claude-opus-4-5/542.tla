---------------------------- MODULE TwoProcessIncrement ----------------------------
EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

vars == <<x, pc>>

Procs == {ProcA, ProcB}

Init == 
    /\ x = 0
    /\ pc = [p \in Procs |-> "inc"]

ProcAAction ==
    /\ pc[ProcA] = "inc"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcA] = "Done"]

ProcBAction ==
    /\ pc[ProcB] = "inc"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcB] = "Done"]

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ProcAAction
    \/ ProcBAction
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInvariant ==
    /\ x \in Int
    /\ pc \in [Procs -> {"inc", "Done"}]

SafetyInvariant ==
    /\ x >= 0
    /\ x <= 2

Termination == <>(\A p \in Procs : pc[p] = "Done")

=============================================================================