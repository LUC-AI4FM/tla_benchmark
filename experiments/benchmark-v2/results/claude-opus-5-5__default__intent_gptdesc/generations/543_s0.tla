------------------------------ MODULE MutexCounter ------------------------------
(***************************************************************************)
(* N identical processes. Each process moves from its noncritical region   *)
(* through a two-step entry protocol into a single critical section. On    *)
(* leaving the critical section it increments a shared counter and then    *)
(* terminates.                                                             *)
(*                                                                         *)
(*   "ncs" -> "e1" -> "e2" -> "cs" -> "done"                               *)
(*                                                                         *)
(*   e1 : announce intent (set the per-process flag)                       *)
(*   e2 : atomically acquire the shared lock if it is free                 *)
(*   cs : increment the counter, release the lock, clear the flag          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs  == 1..N
States == {"ncs", "e1", "e2", "cs", "done"}

VARIABLES
    pc,       \* pc[p] : control state of process p
    flag,     \* flag[p] : per-process local variable (intent to enter)
    lock,     \* shared lock guarding the critical section
    counter   \* shared integer counter

vars == <<pc, flag, lock, counter>>

-----------------------------------------------------------------------------
Init ==
    /\ pc      = [p \in Procs |-> "ncs"]
    /\ flag    = [p \in Procs |-> FALSE]
    /\ lock    = FALSE
    /\ counter = 0

\* Leave the noncritical region and begin the entry protocol.
Leave(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "e1"]
    /\ UNCHANGED <<flag, lock, counter>>

\* Entry step 1: announce intent.
Enter1(p) ==
    /\ pc[p] = "e1"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc'   = [pc EXCEPT ![p] = "e2"]
    /\ UNCHANGED <<lock, counter>>

\* Entry step 2: atomically acquire the lock when it is free.
Enter2(p) ==
    /\ pc[p] = "e2"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ pc'   = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<flag, counter>>

\* Complete the critical section: increment counter, release lock, terminate.
Exit(p) ==
    /\ pc[p] = "cs"
    /\ counter < N
    /\ counter' = counter + 1
    /\ lock'    = FALSE
    /\ flag'    = [flag EXCEPT ![p] = FALSE]
    /\ pc'      = [pc EXCEPT ![p] = "done"]

Proc(p) == Leave(p) \/ Enter1(p) \/ Enter2(p) \/ Exit(p)

\* Once every process has terminated the system stutters (no deadlock).
Terminated ==
    /\ \A p \in Procs : pc[p] = "done"
    /\ UNCHANGED vars

Next == (\E p \in Procs : Proc(p)) \/ Terminated

\* Strong fairness per process: a process whose step is repeatedly enabled
\* (e.g. the lock is repeatedly free while it waits in e2) eventually moves.
Fairness == \A p \in Procs : SF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type and domain invariants                                              *)
(***************************************************************************)
TypeOK ==
    /\ pc      \in [Procs -> States]
    /\ flag    \in [Procs -> BOOLEAN]
    /\ lock    \in BOOLEAN
    /\ counter \in 0..N

LocalDomains ==
    \A p \in Procs : /\ pc[p] \in States
                     /\ flag[p] \in BOOLEAN
                     /\ flag[p] = (pc[p] \in {"e2", "cs"})

(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)
\* Mutual exclusion, stated over ordered pairs of distinct processes.
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* The lock is held exactly when some process is in the critical section.
LockConsistent ==
    lock = (\E p \in Procs : pc[p] = "cs")

CounterInRange == counter \in 0..N

\* The counter equals the number of terminated processes.
CounterMatchesDone ==
    counter = Cardinality({p \in Procs : pc[p] = "done"})

\* When all processes have finished, the counter equals N.
CounterAtTermination ==
    (\A p \in Procs : pc[p] = "done") => counter = N

Safety ==
    /\ TypeOK
    /\ LocalDomains
    /\ MutualExclusion
    /\ LockConsistent
    /\ CounterInRange
    /\ CounterMatchesDone
    /\ CounterAtTermination

THEOREM Spec => []Safety

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
\* Progress: every process attempting to enter eventually enters the
\* critical section or terminates.
Progress ==
    \A p \in Procs :
        (pc[p] \in {"e1", "e2"}) ~> (pc[p] \in {"cs", "done"})

\* Each process eventually leaves the critical section.
CSExit ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "done")

\* Every process eventually terminates.
EachTerminates ==
    \A p \in Procs : <>(pc[p] = "done")

\* All processes eventually terminate together, and stay terminated.
AllTerminate ==
    <>[](\A p \in Procs : pc[p] = "done")

\* At the end, the counter equals N.
EventuallyCounterN ==
    <>[](counter = N)

Liveness ==
    /\ Progress
    /\ CSExit
    /\ EachTerminates
    /\ AllTerminate
    /\ EventuallyCounterN

THEOREM Spec => Liveness
=============================================================================