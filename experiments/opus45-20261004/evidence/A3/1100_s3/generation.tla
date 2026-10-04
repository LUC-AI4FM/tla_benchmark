------------------------------ MODULE MutualExclusion ------------------------------
EXTENDS Integers, TLC

CONSTANTS Proc1, Proc2

VARIABLES pc, lock

vars == <<pc, lock>>

Procs == {Proc1, Proc2}

Locations == {"ncs", "l1", "cs", "l2"}

TypeOK == 
    /\ pc \in [Procs -> Locations]
    /\ lock \in Procs \cup {0}

MutualExclusion == ~(pc[Proc1] = "cs" /\ pc[Proc2] = "cs")

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ lock = 0

\* Non-critical section: move to waiting location l1
ncs(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ lock' = lock

\* Waiting location l1: acquire lock if free and enter critical section
l1(p) ==
    /\ pc[p] = "l1"
    /\ lock = 0
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]

\* Critical section: move to release location l2
cs(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "l2"]
    /\ lock' = lock

\* Release location l2: release lock and return to non-critical section
l2(p) ==
    /\ pc[p] = "l2"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

proc(p) == ncs(p) \/ l1(p) \/ cs(p) \/ l2(p)

Next == \E p \in Procs : proc(p)

Fairness == 
    /\ WF_vars(proc(Proc1))
    /\ WF_vars(proc(Proc2))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Liveness: Process 1 being at l1 leads to eventually reaching cs
Liveness == pc[Proc1] = "l1" ~> pc[Proc1] = "cs"

=============================================================================