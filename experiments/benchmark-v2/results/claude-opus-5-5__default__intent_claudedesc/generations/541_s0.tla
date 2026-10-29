---- MODULE ConcurrentCounter ----
EXTENDS Naturals, TLC

CONSTANTS Procs

ASSUME Procs = {1, 2}

VARIABLES counter, pc, tmp

vars == <<counter, pc, tmp>>

Init ==
    /\ counter = 0
    /\ pc = [p \in Procs |-> "read"]
    /\ tmp = [p \in Procs |-> 0]

Read(p) ==
    /\ pc[p] = "read"
    /\ tmp' = [tmp EXCEPT ![p] = counter]
    /\ pc' = [pc EXCEPT ![p] = "write"]
    /\ UNCHANGED counter

Write(p) ==
    /\ pc[p] = "write"
    /\ counter' = tmp[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED tmp

Terminating ==
    /\ \A p \in Procs : pc[p] = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Read(p) \/ Write(p)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(Read(p) \/ Write(p))

TypeOK ==
    /\ counter \in 0..2
    /\ pc \in [Procs -> {"read", "write", "done"}]
    /\ tmp \in [Procs -> 0..2]

AllDone == \A p \in Procs : pc[p] = "done"

AdditionCorrect == AllDone => counter = 2

Termination == <>AllDone

====