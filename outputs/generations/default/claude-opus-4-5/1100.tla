------------------------------- MODULE MutualExclusion -------------------------------
EXTENDS Integers, TLC

CONSTANTS Procs

VARIABLES pc, lock

vars == <<pc, lock>>

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ lock = "free"

NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ lock' = lock

L1(p) ==
    /\ pc[p] = "l1"
    /\ lock = "free"
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]

CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "l2"]
    /\ lock' = lock

L2(p) ==
    /\ pc[p] = "l2"
    /\ lock' = "free"
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

proc(p) ==
    \/ NCS(p)
    \/ L1(p)
    \/ CS(p)
    \/ L2(p)

Next ==
    \E p \in Procs : proc(p)

Fairness ==
    \A p \in Procs : WF_vars(proc(p))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "l1", "cs", "l2"}]
    /\ lock \in Procs \cup {"free"}

MutualExclusion ==
    \A p1, p2 \in Procs : (p1 # p2) => ~(pc[p1] = "cs" /\ pc[p2] = "cs")

Liveness ==
    (1 \in Procs) => (pc[1] = "l1" ~> pc[1] = "cs")

=============================================================================