---------------------------- MODULE TwoProcessIncrement ----------------------------
EXTENDS Integers, TLC

VARIABLES x, pc

vars == <<x, pc>>

ProcSet == {"ProcA", "ProcB"}

Init ==
    /\ x = 0
    /\ pc = [p \in ProcSet |-> "inc"]

ProcA ==
    /\ pc["ProcA"] = "inc"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

ProcB ==
    /\ pc["ProcB"] = "inc"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

Terminating ==
    /\ \A p \in ProcSet : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ProcA
    \/ ProcB
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInvariant ==
    /\ x \in 0..2
    /\ pc \in [ProcSet -> {"inc", "Done"}]

SafetyInvariant ==
    /\ x >= 0
    /\ x <= 2

Termination == <>(\A p \in ProcSet : pc[p] = "Done")

===================================================================================