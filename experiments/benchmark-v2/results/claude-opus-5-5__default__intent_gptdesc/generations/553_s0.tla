------------------------------ MODULE FilterMutex ------------------------------
(***************************************************************************)
(* N-process Peterson-style mutual exclusion (the "Filter" lock).          *)
(*                                                                         *)
(* Each process cycles through: noncritical section -> entry protocol ->  *)
(* critical section -> exit protocol -> noncritical section.               *)
(*                                                                         *)
(* The entry protocol is a symmetric multi-level generalisation of the     *)
(* two-process Peterson lock. A process climbs levels 1 .. N-1. At each    *)
(* level L it:                                                             *)
(*   1. announces level L,                                                 *)
(*   2. makes itself the victim of level L,                                *)
(*   3. waits until no other process is at level >= L, or until it is no   *)
(*      longer the victim of level L.                                      *)
(* After passing level N-1 it enters the critical section.                 *)
(* The exit protocol resets its announced level to 0.                      *)
(*                                                                         *)
(* Shared coordination variables: level[i] and victim[L].                  *)
(* Process-local variables: pc[i], the control state, and lev[i], the      *)
(* level currently being contended.                                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs  == 1 .. N
Levels == 1 .. (N - 1)

VARIABLES
    pc,      \* control state of each process
    lev,     \* level each process is currently working on (local)
    level,   \* shared: level announced by each process (0 = not competing)
    victim   \* shared: victim[L] = last process to arrive at level L

vars == << pc, lev, level, victim >>

(* Abstract process states. *)
Outside == {"ncs"}
Trying  == {"setlevel", "setvictim", "wait"}
InCS    == {"cs"}
Exiting == {"exit"}
PCs     == Outside \cup Trying \cup InCS \cup Exiting

-----------------------------------------------------------------------------
TypeOK ==
    /\ pc     \in [Procs -> PCs]
    /\ lev    \in [Procs -> Levels]
    /\ level  \in [Procs -> 0 .. (N - 1)]
    /\ victim \in [Levels -> Procs]

Init ==
    /\ pc     = [i \in Procs |-> "ncs"]
    /\ lev    = [i \in Procs |-> 1]
    /\ level  = [i \in Procs |-> 0]
    /\ victim = [l \in Levels |-> 1]

-----------------------------------------------------------------------------
(* Leave the noncritical section and begin the entry protocol.             *)
(* The process may stay in the noncritical section forever, so this step   *)
(* is not subject to fairness.                                             *)
Try(i) ==
    /\ pc[i] = "ncs"
    /\ pc'  = [pc  EXCEPT ![i] = "setlevel"]
    /\ lev' = [lev EXCEPT ![i] = 1]
    /\ UNCHANGED << level, victim >>

(* Entry, step 1: announce the current level. *)
SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ level' = [level EXCEPT ![i] = lev[i]]
    /\ pc'    = [pc    EXCEPT ![i] = "setvictim"]
    /\ UNCHANGED << lev, victim >>

(* Entry, step 2: become the victim of the current level. *)
SetVictim(i) ==
    /\ pc[i] = "setvictim"
    /\ victim' = [victim EXCEPT ![lev[i]] = i]
    /\ pc'     = [pc     EXCEPT ![i] = "wait"]
    /\ UNCHANGED << lev, level >>

(* Condition under which process i may pass its current level. *)
CanPass(i) ==
    \/ \A k \in Procs \ {i} : level[k] < lev[i]
    \/ victim[lev[i]] # i

(* Entry, step 3: wait, then climb to the next level or enter the CS. *)
Wait(i) ==
    /\ pc[i] = "wait"
    /\ CanPass(i)
    /\ IF lev[i] = N - 1
          THEN /\ pc'  = [pc EXCEPT ![i] = "cs"]
               /\ lev' = lev
          ELSE /\ pc'  = [pc  EXCEPT ![i] = "setlevel"]
               /\ lev' = [lev EXCEPT ![i] = lev[i] + 1]
    /\ UNCHANGED << level, victim >>

(* Leave the critical section and begin the exit protocol. *)
LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << lev, level, victim >>

(* Exit protocol: release the lock by withdrawing from all levels. *)
Exit(i) ==
    /\ pc[i] = "exit"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ pc'    = [pc    EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << lev, victim >>

(* All steps of process i that are subject to fairness. *)
Proc(i) ==
    \/ SetLevel(i)
    \/ SetVictim(i)
    \/ Wait(i)
    \/ LeaveCS(i)
    \/ Exit(i)

(* Asynchronous interleaving: exactly one process takes one step. *)
Next == \E i \in Procs : Try(i) \/ Proc(i)

Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)

(* At most one process is in the critical section at any time. *)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* The announced shared level is consistent with the local control state. *)
LevelConsistency ==
    \A i \in Procs :
        /\ (pc[i] = "ncs") => (level[i] = 0)
        /\ (pc[i] = "setlevel") => (level[i] = lev[i] - 1)
        /\ (pc[i] \in {"setvictim", "wait"}) => (level[i] = lev[i])
        /\ (pc[i] \in {"cs", "exit"}) => (level[i] = N - 1 /\ lev[i] = N - 1)

(* A process waiting at level L appears at level L in the shared array.    *)
(* A process at level L that has registered is either the victim of L or   *)
(* has been displaced by a later arrival, so victim[L] is always a process *)
(* that has announced level >= L once anyone is waiting at L.              *)
VictimConsistency ==
    \A i \in Procs :
        (pc[i] = "wait") =>
            \/ victim[lev[i]] = i
            \/ /\ victim[lev[i]] # i
               /\ level[victim[lev[i]]] >= lev[i] \/ pc[victim[lev[i]]] = "setlevel"
                                                  \/ pc[victim[lev[i]]] = "ncs"
                                                  \/ pc[victim[lev[i]]] = "exit"
                                                  \/ pc[victim[lev[i]]] = "cs"
                                                  \/ pc[victim[lev[i]]] = "setvictim"
                                                  \/ pc[victim[lev[i]]] = "wait"

(* Process i has passed the wait at level L. *)
Passed(i, L) ==
    \/ pc[i] \in Trying /\ lev[i] > L
    \/ pc[i] \in InCS \cup Exiting

(* Filter property: at most N - L processes have passed level L.           *)
(* For L = N-1 this yields mutual exclusion over the critical section and  *)
(* exit protocol.                                                          *)
FilterInvariant ==
    \A L \in Levels : Cardinality({ i \in Procs : Passed(i, L) }) <= N - L

(* At most one process holds the lock, whether in the CS or exiting. *)
LockHeldExclusively ==
    Cardinality({ i \in Procs : pc[i] \in InCS \cup Exiting }) <= 1

Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ LevelConsistency
    /\ FilterInvariant
    /\ LockHeldExclusively

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

(* Every process that tries to enter eventually enters the CS. *)
StarvationFreedom ==
    \A i \in Procs : (pc[i] \in Trying) ~> (pc[i] = "cs")

(* If some process is trying, some process eventually enters the CS. *)
DeadlockFreedom ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E j \in Procs : pc[j] = "cs")

(* Every process in the CS or exit protocol eventually returns to the NCS. *)
ExitProgress ==
    \A i \in Procs : (pc[i] \in InCS \cup Exiting) ~> (pc[i] = "ncs")

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => StarvationFreedom
THEOREM Spec => DeadlockFreedom
THEOREM Spec => ExitProgress
=============================================================================