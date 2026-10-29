---------------------------- MODULE MCSession9sem ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

VARIABLES sem, pc

vars == << sem, pc >>

ConstN == 3
ConstProcs == {0, 1, 2}

-----------------------------------------------------------------------------
(* Semaphore-based mutual exclusion algorithm *)

Init == /\ sem = 1
        /\ pc = [p \in Procs |-> "ncs"]

NCS(p) == /\ pc[p] = "ncs"
          /\ pc' = [pc EXCEPT ![p] = "enter"]
          /\ UNCHANGED sem

Enter(p) == /\ pc[p] = "enter"
            /\ sem > 0
            /\ sem' = sem - 1
            /\ pc' = [pc EXCEPT ![p] = "cs"]

Exit(p) == /\ pc[p] = "cs"
           /\ sem' = sem + 1
           /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) == NCS(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : /\ SF_vars(Enter(p))
                            /\ WF_vars(Exit(p))

-----------------------------------------------------------------------------
(* Properties *)

TypeOK == /\ sem \in 0..1
          /\ pc \in [Procs -> {"ncs", "enter", "cs"}]

MutualExclusion == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] = "enter") ~> (\E p \in Procs : pc[p] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

=============================================================================