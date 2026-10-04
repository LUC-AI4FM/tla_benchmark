---- MODULE TwoProcessIncrement ----

EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

vars == <<x, pc>>

Procs == {ProcA, ProcB}

Init ==
    /\ x = 0
    /\ pc = [p \in Procs |-> "Inc"]

ProcAInc ==
    /\ pc[ProcA] = "Inc"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcA] = "Done"]

ProcBInc ==
    /\ pc[ProcB] = "Inc"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcB] = "Done"]

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ProcAInc
    \/ ProcBInc
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInvariant ==
    /\ x \in Nat
    /\ pc \in [Procs -> {"Inc", "Done"}]

SafetyInvariant ==
    /\ x >= 0
    /\ x <= 2

Termination == <>(\A p \in Procs : pc[p] = "Done")

====