------------------------------ MODULE Semaphore ------------------------------
(***************************************************************************)
(* A binary semaphore used to implement mutual exclusion among N          *)
(* processes. Each process repeatedly cycles through these phases:        *)
(*   "ncs"   : non-critical section (may stay here forever)               *)
(*   "enter" : trying to acquire the semaphore (P operation)              *)
(*   "cs"    : critical section                                           *)
(*   "exit"  : releasing the semaphore (V operation)                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES sem,   \* the binary semaphore: 1 = available, 0 = held
          pc     \* pc[p] is the current phase of process p

vars == <<sem, pc>>

Phases == {"ncs", "enter", "cs", "exit"}

-----------------------------------------------------------------------------
TypeOK ==
    /\ sem \in {0, 1}
    /\ pc \in [Procs -> Phases]

Init ==
    /\ sem = 1
    /\ pc = [p \in Procs |-> "ncs"]

(* Leave the non-critical section and start trying to enter. *)
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED sem

(* Atomically check that the semaphore is available and claim it. *)
Enter(p) ==
    /\ pc[p] = "enter"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "cs"]

(* Do the critical-section work and move to the exit phase. *)
CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED sem

(* Release the semaphore and return to the non-critical section. *)
Exit(p) ==
    /\ pc[p] = "exit"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) == NCS(p) \/ Enter(p) \/ CS(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

(***************************************************************************)
(* Fairness:                                                              *)
(*  - No fairness on NCS(p): a process may stay in its non-critical       *)
(*    section forever.                                                    *)
(*  - Weak fairness on the other non-NCS steps (CS, Exit).                *)
(*  - Strong fairness on Enter(p), because it is only intermittently      *)
(*    enabled as the semaphore is acquired and released by others.       *)
(***************************************************************************)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(CS(p))
        /\ WF_vars(Exit(p))
        /\ SF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* The semaphore is held exactly when some process is in cs or exit. *)
SemaphoreConsistent ==
    /\ (sem = 0) <=> (\E p \in Procs : pc[p] \in {"cs", "exit"})
    /\ \A p, q \in Procs :
         (p # q) => ~(pc[p] \in {"cs", "exit"} /\ pc[q] \in {"cs", "exit"})

Inv == TypeOK /\ MutualExclusion /\ SemaphoreConsistent

(* Liveness property *)

StarvationFreedom ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

(* Every process that enters the critical section eventually leaves it. *)
EventuallyRelease ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs")

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => StarvationFreedom
=============================================================================