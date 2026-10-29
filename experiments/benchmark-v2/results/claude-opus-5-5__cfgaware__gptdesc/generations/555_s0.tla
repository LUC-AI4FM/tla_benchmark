---------------------------- MODULE MCSession9sem ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == 0..(ConstN - 1)

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in {0, 1}
    /\ pc \in [Procs -> {"ncs", "wait", "cs"}]

Init ==
    /\ sem = 1
    /\ pc = [p \in Procs |-> "ncs"]

Request(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED sem

Enter(p) ==
    /\ pc[p] = "wait"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "cs"]

Exit(p) ==
    /\ pc[p] = "cs"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Next == \E p \in Procs : Request(p) \/ Enter(p) \/ Exit(p)

Fairness ==
    \A p \in Procs :
        /\ SF_vars(Enter(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] = "wait") ~> (\E p \in Procs : pc[p] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

=============================================================================