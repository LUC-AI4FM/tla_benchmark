---------------------------- MODULE MCSession9sem ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the semaphore-based mutual exclusion         *)
(* protocol Session9sem.  The protocol is inlined here so the module is    *)
(* self-contained.  It fixes the number of processes to 3, defines the     *)
(* process set as 0..(ConstN-1), and states the following properties:      *)
(*   - mutual exclusion (safety),                                          *)
(*   - deadlock/livelock freedom (leads-to liveness),                      *)
(*   - starvation freedom (leads-to liveness),                             *)
(* all expressed over the process control-state variable pc.               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ConstN == 3

ConstProcSet == 0..(ConstN - 1)

ProcSet == ConstProcSet

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in 0..1
    /\ pc \in [ProcSet -> {"ncs", "wait", "cs"}]

Init ==
    /\ sem = 1
    /\ pc = [p \in ProcSet |-> "ncs"]

Request(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED sem

Acquire(p) ==
    /\ pc[p] = "wait"
    /\ sem > 0
    /\ sem' = sem - 1
    /\ pc' = [pc EXCEPT ![p] = "cs"]

Release(p) ==
    /\ pc[p] = "cs"
    /\ sem' = sem + 1
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) == Request(p) \/ Acquire(p) \/ Release(p)

Next == \E p \in ProcSet : Proc(p)

Fairness ==
    \A p \in ProcSet : WF_vars(Acquire(p)) /\ WF_vars(Release(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: at most one process is in its critical section. *)
MutualExclusion ==
    \A p, q \in ProcSet : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

(* Deadlock/livelock freedom: if some process is trying to enter, *)
(* then eventually some process enters its critical section.      *)
DeadlockFree ==
    (\E p \in ProcSet : pc[p] = "wait") ~> (\E p \in ProcSet : pc[p] = "cs")

(* Starvation freedom: every process that tries to enter *)
(* eventually enters its critical section.               *)
StarvationFree ==
    \A p \in ProcSet : (pc[p] = "wait") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================