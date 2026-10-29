---- MODULE ConcurrentIncrement ----
EXTENDS Naturals, TLC

CONSTANTS Procs

ASSUME Procs = {1, 2}

VARIABLES x, pc

vars == <<x, pc>>

TypeOK ==
    /\ x \in Nat
    /\ pc \in [Procs -> {"inc", "Done"}]

Init ==
    /\ x = 0
    /\ pc = [p \in Procs |-> "inc"]

Inc(p) ==
    /\ pc[p] = "inc"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Inc(p)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs : WF_vars(Inc(p))

Termination == <>(\A p \in Procs : pc[p] = "Done")

====