------------------------------ MODULE SemaphoreMutex ------------------------------
(***************************************************************************)
(* N identical processes share one critical region, guarded by a binary    *)
(* semaphore. Each process cycles through four high-level states:          *)
(*   "noncrit"   - doing noncritical work                                  *)
(*   "waiting"   - trying to acquire the semaphore                         *)
(*   "critical"  - in the critical region (holds the semaphore)            *)
(*   "releasing" - has released the semaphore and is returning to          *)
(*                 noncritical work                                        *)
(* The semaphore is acquired atomically, and only when it is available     *)
(* (sem = 1). Acquiring it sets sem to 0. The holder sets sem back to 1    *)
(* when it leaves the critical region.                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES pc,   \* pc[p] : high-level state of process p
          sem   \* binary semaphore: 1 = available, 0 = unavailable

vars == <<pc, sem>>

Procs  == 1..N
States == {"noncrit", "waiting", "critical", "releasing"}

TypeOK ==
    /\ pc  \in [Procs -> States]
    /\ sem \in {0, 1}

Init ==
    /\ pc  = [p \in Procs |-> "noncrit"]
    /\ sem = 1

(* Finish noncritical work and start trying to enter. *)
Try(p) ==
    /\ pc[p] = "noncrit"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED sem

(* Atomic semaphore acquisition (P operation): enabled only if available. *)
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "critical"]

(* Leave the critical region and release the semaphore (V operation). *)
Exit(p) ==
    /\ pc[p] = "critical"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "releasing"]

(* Finish releasing and go back to noncritical work. *)
Return(p) ==
    /\ pc[p] = "releasing"
    /\ pc' = [pc EXCEPT ![p] = "noncrit"]
    /\ UNCHANGED sem

Proc(p) == Try(p) \/ Enter(p) \/ Exit(p) \/ Return(p)

(* Asynchronous interleaving: exactly one process takes a step at a time. *)
Next == \E p \in Procs : Proc(p)

(***************************************************************************)
(* Fairness:                                                               *)
(*  - Weak fairness on Try, Exit and Return. A process does not halt       *)
(*    forever in noncrit, critical or releasing, so it keeps trying again. *)
(*  - Strong fairness on Enter. If the semaphore is available infinitely   *)
(*    often while p is waiting, p eventually acquires it, so it is not     *)
(*    starved.                                                             *)
(***************************************************************************)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(Try(p))
        /\ SF_vars(Enter(p))
        /\ WF_vars(Exit(p))
        /\ WF_vars(Return(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

InCS == {p \in Procs : pc[p] = "critical"}

(* Mutual exclusion: at most one process is in the critical region. *)
MutualExclusion == Cardinality(InCS) <= 1

(* The semaphore is unavailable iff some process is in the critical region. *)
SemaphoreAccurate == (sem = 0) <=> (\E p \in Procs : pc[p] = "critical")

(* No deadlock: some action is always enabled. *)
NoDeadlock == ENABLED Next

Invariants == TypeOK /\ MutualExclusion /\ SemaphoreAccurate

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ SemaphoreAccurate /\ NoDeadlock)

---------------------------------------------------------------------------
(* Liveness properties *)

(* Starvation freedom: a process that keeps trying eventually enters. *)
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "waiting") ~> (pc[p] = "critical")

(* Deadlock freedom: if some process is waiting, some process eventually enters. *)
DeadlockFreedom ==
    (\E p \in Procs : pc[p] = "waiting") ~> (\E p \in Procs : pc[p] = "critical")

(* The semaphore never becomes permanently unavailable. *)
SemaphoreEventuallyAvailable == []<>(sem = 1)

(* Every process repeatedly returns to noncritical work and tries again. *)
Repetition ==
    \A p \in Procs : /\ []<>(pc[p] = "noncrit")
                     /\ []<>(pc[p] = "waiting")

(* Every process enters the critical region infinitely often. *)
InfinitelyOftenCritical ==
    \A p \in Procs : []<>(pc[p] = "critical")

THEOREM Spec => /\ StarvationFreedom
                /\ DeadlockFreedom
                /\ SemaphoreEventuallyAvailable
                /\ Repetition
                /\ InfinitelyOftenCritical
=============================================================================