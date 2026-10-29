--------------------------- MODULE MCSession9sem ---------------------------
(***************************************************************************)
(* Model-checking configuration for a semaphore-based mutual exclusion     *)
(* algorithm (base algorithm of Session9sem, inlined here so the module    *)
(* is self-contained). The constant N is intended to be instantiated with  *)
(* const_N == 3, giving the process set Procs = {0, 1, 2}.                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

const_N == 3

ASSUME N \in Nat \ {0}

Procs == 0 .. (N - 1)

VARIABLES pc, sem

vars == <<pc, sem>>

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "enter", "cs"}]
    /\ sem \in {0, 1}

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ sem = 1

\* A process leaves its non-critical section and tries to enter.
Try(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED sem

\* P(sem): acquire the semaphore and enter the critical section.
Enter(p) ==
    /\ pc[p] = "enter"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "cs"]

\* V(sem): leave the critical section and release the semaphore.
Exit(p) ==
    /\ pc[p] = "cs"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) == Try(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Exit(p))
        /\ SF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] = "enter") ~> (\E p \in Procs : pc[p] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadAndLivelockFree /\ StarvationFree
=============================================================================