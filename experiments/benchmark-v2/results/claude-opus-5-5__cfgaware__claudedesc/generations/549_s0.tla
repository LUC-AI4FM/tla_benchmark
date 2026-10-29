---------------------------- MODULE MCSession9alt ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

VARIABLES pc, lock

vars == <<pc, lock>>

ConstN == 3

ConstProcs == {0, 1, 2}

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "try", "cs"}]
    /\ lock \in BOOLEAN

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ lock = FALSE

Request(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ UNCHANGED lock

Enter(p) ==
    /\ pc[p] = "try"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "cs"]

Exit(p) ==
    /\ pc[p] = "cs"
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Next == \E p \in Procs : Request(p) \/ Enter(p) \/ Exit(p)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Request(p))
        /\ SF_vars(Enter(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

LivenessNaive ==
    \A i \in Procs : []<>(pc[i] = "cs")

=============================================================================