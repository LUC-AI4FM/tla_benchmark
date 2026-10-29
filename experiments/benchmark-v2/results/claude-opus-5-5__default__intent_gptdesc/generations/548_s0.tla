---------------------------- MODULE FilterMutex ----------------------------
(***************************************************************************)
(* N-process mutual exclusion via the Peterson "filter" algorithm.         *)
(* Each process climbs entry levels 0..N-2. At each level it announces     *)
(* its level, records itself as the last to enter that level (victim),     *)
(* and waits while some other process is at the same or a higher level     *)
(* and it is still the last to enter. A process that passes level N-2      *)
(* enters the critical section. On exit it gives up its level claim.       *)
(*                                                                         *)
(* The value -1 means "no level". The value 0 in last[l] means "no         *)
(* process yet". When N = 1 there are no levels, so the single process     *)
(* enters the critical section directly.                                   *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs   == 1..N
Levels  == 0..(N-2)            \* empty when N = 1
NoLevel == -1
NoProc  == 0

VARIABLES
    level,   \* level[p] : announced level of p (NoLevel if not competing)
    last,    \* last[l]  : last process to enter level l
    lv,      \* lv[p]    : level p is currently working on (local variable)
    pc       \* pc[p]    : program counter of p

vars == <<level, last, lv, pc>>

PCs == {"ncs", "announce", "setlast", "wait", "cs", "exit"}

Trying(p) == pc[p] \in {"announce", "setlast", "wait"}

TypeOK ==
    /\ level \in [Procs -> Levels \cup {NoLevel}]
    /\ last  \in [Levels -> Procs \cup {NoProc}]
    /\ lv    \in [Procs -> Levels \cup {NoLevel}]
    /\ pc    \in [Procs -> PCs]

Init ==
    /\ level = [p \in Procs  |-> NoLevel]
    /\ last  = [l \in Levels |-> NoProc]
    /\ lv    = [p \in Procs  |-> NoLevel]
    /\ pc    = [p \in Procs  |-> "ncs"]

(* Leave the noncritical section and request entry *)
Request(p) ==
    /\ pc[p] = "ncs"
    /\ IF N = 1
         THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED lv
         ELSE /\ lv' = [lv EXCEPT ![p] = 0]
              /\ pc' = [pc EXCEPT ![p] = "announce"]
    /\ UNCHANGED <<level, last>>

(* Announce the current level *)
Announce(p) ==
    /\ pc[p] = "announce"
    /\ level' = [level EXCEPT ![p] = lv[p]]
    /\ pc' = [pc EXCEPT ![p] = "setlast"]
    /\ UNCHANGED <<last, lv>>

(* Record self as last to enter this level *)
SetLast(p) ==
    /\ pc[p] = "setlast"
    /\ last' = [last EXCEPT ![lv[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<level, lv>>

(* Waiting condition at the current level:
   proceed once no other process is at the same or a higher level,
   or once some other process has become the last to enter this level. *)
CanProceed(p) ==
    \/ \A k \in Procs \ {p} : level[k] < lv[p]
    \/ last[lv[p]] # p

Wait(p) ==
    /\ pc[p] = "wait"
    /\ CanProceed(p)
    /\ IF lv[p] = N - 2
         THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED lv
         ELSE /\ lv' = [lv EXCEPT ![p] = lv[p] + 1]
              /\ pc' = [pc EXCEPT ![p] = "announce"]
    /\ UNCHANGED <<level, last>>

(* Leave the critical section *)
LeaveCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<level, last, lv>>

(* Exit protocol: give up the level claim *)
Exit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = NoLevel]
    /\ lv' = [lv EXCEPT ![p] = NoLevel]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED last

(* All steps of p except Request. A process may stay in its noncritical
   section forever, so Request has no fairness. *)
ProtocolStep(p) ==
    \/ Announce(p)
    \/ SetLast(p)
    \/ Wait(p)
    \/ LeaveCS(p)
    \/ Exit(p)

Proc(p) == Request(p) \/ ProtocolStep(p)

Next == \E p \in Procs : Proc(p)

(* Fairness:
   - Weak fairness on the protocol steps of each process. This also means
     processes always eventually leave the CS.
   - Strong fairness on Wait. The waiting condition can be enabled and
     disabled repeatedly by other processes, so p must eventually be
     scheduled when it is repeatedly able to proceed. *)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(ProtocolStep(p))
        /\ SF_vars(Wait(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: mutual exclusion *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Structural invariant of the filter: at most N - l processes have
   reached level l or beyond. Counting processes in the CS as level N-1. *)
EffLevel(p) == IF pc[p] \in {"cs", "exit"} THEN N - 1 ELSE level[p]

FilterInv ==
    \A l \in 0..(N-1) :
        Cardinality({p \in Procs : EffLevel(p) >= l}) <= N - l

(* Deadlock freedom (state form): if some process is in its entry or exit
   protocol or in the CS, then some process can take a step. *)
NoDeadlock ==
    (\E p \in Procs : pc[p] # "ncs") =>
        (\E p \in Procs : ENABLED ProtocolStep(p))

DeadlockFreedomProp == []NoDeadlock

(* Deadlock freedom (progress form): if some process is trying, then
   some process eventually enters the critical section. *)
DeadlockFreedom ==
    (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : pc[p] = "cs")

(* Starvation freedom: every process that tries eventually enters the CS. *)
StarvationFreedom ==
    \A p \in Procs : Trying(p) ~> (pc[p] = "cs")

(* Every process in the CS eventually returns to its noncritical section. *)
ExitProgress ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ FilterInv)
THEOREM Spec => DeadlockFreedomProp
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom /\ ExitProgress
=============================================================================