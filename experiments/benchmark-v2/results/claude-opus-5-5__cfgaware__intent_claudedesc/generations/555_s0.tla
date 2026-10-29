---------------------------- MODULE Semaphore ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == 0 .. (ConstN - 1)

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in {0, 1}
    /\ pc \in [Procs -> {"idle", "waiting", "cs"}]

Init ==
    /\ sem = 1
    /\ pc = [p \in Procs |-> "idle"]

Try(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED sem

Acquire(p) ==
    /\ pc[p] = "waiting"
    /\ sem > 0
    /\ sem' = sem - 1
    /\ pc' = [pc EXCEPT ![p] = "cs"]

Release(p) ==
    /\ pc[p] = "cs"
    /\ sem' = sem + 1
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Next == \E p \in Procs : Try(p) \/ Acquire(p) \/ Release(p)

Fairness ==
    \A p \in Procs : /\ SF_vars(Acquire(p))
                     /\ WF_vars(Release(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] = "waiting") ~> (\E p \in Procs : pc[p] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] = "waiting") ~> (pc[p] = "cs")

=============================================================================