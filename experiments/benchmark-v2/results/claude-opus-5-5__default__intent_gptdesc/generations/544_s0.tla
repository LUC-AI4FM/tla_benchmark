------------------------------ MODULE GuardedCounter ------------------------------
(***************************************************************************)
(* N identical processes each perform, exactly once, a guarded increment  *)
(* of a shared counter under mutual exclusion provided by a binary        *)
(* semaphore:                                                             *)
(*     acquire ; tmp := counter ; tmp := tmp + 1 ; counter := tmp ;       *)
(*     release                                                            *)
(* The lock is modeled abstractly: any process can acquire it when it is  *)
(* free (sem = 1), and only one process can hold it (sem = 0).            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs == 1..N

VARIABLES
    counter,   \* shared integer counter
    sem,       \* binary semaphore: 1 = unlocked, 0 = locked
    pc,        \* per-process program counter
    tmp        \* per-process local temporary (abstract)

vars == <<counter, sem, pc, tmp>>

Labels == {"acq", "read", "inc", "write", "rel", "Done"}

\* Locations that lie inside the critical section (lock held).
CS == {"read", "inc", "write", "rel"}

\* Processes that have completed their write to the shared counter.
Completed == {p \in Procs : pc[p] \in {"rel", "Done"}}

InCS == {p \in Procs : pc[p] \in CS}

-----------------------------------------------------------------------------

TypeOK ==
    /\ counter \in 0..N
    /\ sem \in {0, 1}
    /\ pc \in [Procs -> Labels]
    /\ tmp \in [Procs -> 0..(N + 1)]

Init ==
    /\ counter = 0
    /\ sem = 1
    /\ pc = [p \in Procs |-> "acq"]
    /\ tmp = [p \in Procs |-> 0]

\* Acquire the lock (blocking until it is free).
Acquire(p) ==
    /\ pc[p] = "acq"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "read"]
    /\ UNCHANGED <<counter, tmp>>

\* Read the shared counter into the local temporary.
Read(p) ==
    /\ pc[p] = "read"
    /\ tmp' = [tmp EXCEPT ![p] = counter]
    /\ pc' = [pc EXCEPT ![p] = "inc"]
    /\ UNCHANGED <<counter, sem>>

\* Compute temporary + 1 locally.
Inc(p) ==
    /\ pc[p] = "inc"
    /\ tmp' = [tmp EXCEPT ![p] = tmp[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "write"]
    /\ UNCHANGED <<counter, sem>>

\* Write the local value back to the shared counter.
Write(p) ==
    /\ pc[p] = "write"
    /\ counter' = tmp[p]
    /\ pc' = [pc EXCEPT ![p] = "rel"]
    /\ UNCHANGED <<sem, tmp>>

\* Release the lock and terminate.
Release(p) ==
    /\ pc[p] = "rel"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<counter, tmp>>

Proc(p) == Acquire(p) \/ Read(p) \/ Inc(p) \/ Write(p) \/ Release(p)

AllDone == \A p \in Procs : pc[p] = "Done"

\* Once all processes have terminated, the system may only stutter.
Terminating == AllDone /\ UNCHANGED vars

Next == (\E p \in Procs : Proc(p)) \/ Terminating

\* Weak fairness on each process's steps; strong fairness on acquisition
\* so that no process is starved by others repeatedly taking the lock.
Fairness ==
    \A p \in Procs :
        /\ WF_vars(Proc(p))
        /\ SF_vars(Acquire(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)

\* At most one process is in the critical section.
MutualExclusion == Cardinality(InCS) <= 1

\* The semaphore is 0 exactly when one process holds it; never "held"
\* by more than one process.
SemaphoreConsistent ==
    /\ (sem = 0) <=> (Cardinality(InCS) = 1)
    /\ (sem = 1) <=> (InCS = {})

\* No lost or duplicated increments.
CounterCorrect == counter = Cardinality(Completed)

\* Local temporary is consistent with the shared counter inside the CS.
TmpConsistent ==
    \A p \in Procs :
        /\ pc[p] = "inc"   => tmp[p] = counter
        /\ pc[p] = "write" => tmp[p] = counter + 1

Safety ==
    /\ TypeOK
    /\ MutualExclusion
    /\ SemaphoreConsistent
    /\ CounterCorrect
    /\ TmpConsistent

(***************************************************************************)
(* Liveness properties                                                    *)
(***************************************************************************)

\* Every process attempting to enter eventually completes (no starvation).
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "acq") ~> (pc[p] = "Done")

\* Every process that enters the critical section eventually leaves it.
CSProgress ==
    \A p \in Procs : (pc[p] \in CS) ~> (pc[p] = "Done")

\* All processes eventually terminate.
EventualTermination == <>AllDone

\* Final result: the counter eventually equals N.
FinalCounter == <>(counter = N)

(***************************************************************************)
(* Termination / stability: once all are done, the state stays stable.    *)
(***************************************************************************)

StableTermination ==
    [](AllDone => [](AllDone /\ counter = N /\ sem = 1))

Liveness ==
    /\ StarvationFreedom
    /\ CSProgress
    /\ EventualTermination
    /\ FinalCounter

-----------------------------------------------------------------------------

THEOREM Spec => []Safety
THEOREM Spec => Liveness
THEOREM Spec => StableTermination

=============================================================================