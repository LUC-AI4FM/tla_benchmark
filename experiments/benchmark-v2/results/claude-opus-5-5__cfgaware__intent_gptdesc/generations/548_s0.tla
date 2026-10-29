---------------------------- MODULE FilterMutex ----------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs  == 1..N
Levels == 0..(N-2)

VARIABLES
    pc,      \* program counter of each process
    level,   \* announced level of each process (-1 = no level / not competing)
    last,    \* last[l] = last process to enter level l
    lvl      \* level the process is currently trying to pass

vars == <<pc, level, last, lvl>>

PCs == {"ncs", "setlevel", "setlast", "wait", "cs", "exit"}

TypeOK ==
    /\ pc    \in [Procs -> PCs]
    /\ level \in [Procs -> -1..(N-2)]
    /\ last  \in [Levels -> Procs]
    /\ lvl   \in [Procs -> 0..(IF N > 1 THEN N-2 ELSE 0)]

Init ==
    /\ pc    = [i \in Procs |-> "ncs"]
    /\ level = [i \in Procs |-> -1]
    /\ last  = [l \in Levels |-> CHOOSE p \in Procs : TRUE]
    /\ lvl   = [i \in Procs |-> 0]

(* Leave the noncritical section and start the entry protocol *)
StartEntry(i) ==
    /\ pc[i] = "ncs"
    /\ IF N = 1
         THEN pc' = [pc EXCEPT ![i] = "cs"]
         ELSE pc' = [pc EXCEPT ![i] = "setlevel"]
    /\ lvl' = [lvl EXCEPT ![i] = 0]
    /\ UNCHANGED <<level, last>>

(* Announce the level *)
SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ level' = [level EXCEPT ![i] = lvl[i]]
    /\ pc' = [pc EXCEPT ![i] = "setlast"]
    /\ UNCHANGED <<last, lvl>>

(* Record self as last to enter this level *)
SetLast(i) ==
    /\ pc[i] = "setlast"
    /\ last' = [last EXCEPT ![lvl[i]] = i]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED <<level, lvl>>

(* Wait until no conflicting process at same/higher level, or no longer last *)
CanProceed(i) ==
    \/ \A k \in Procs \ {i} : level[k] < lvl[i]
    \/ last[lvl[i]] # i

Wait(i) ==
    /\ pc[i] = "wait"
    /\ CanProceed(i)
    /\ IF lvl[i] = N - 2
         THEN /\ pc'  = [pc EXCEPT ![i] = "cs"]
              /\ lvl' = lvl
         ELSE /\ pc'  = [pc EXCEPT ![i] = "setlevel"]
              /\ lvl' = [lvl EXCEPT ![i] = lvl[i] + 1]
    /\ UNCHANGED <<level, last>>

(* Leave the critical section *)
LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<level, last, lvl>>

(* Exit: relinquish entry claims *)
Exit(i) ==
    /\ pc[i] = "exit"
    /\ level' = [level EXCEPT ![i] = -1]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ lvl' = [lvl EXCEPT ![i] = 0]
    /\ UNCHANGED last

(* All steps other than leaving the noncritical section *)
Progress(i) ==
    \/ SetLevel(i)
    \/ SetLast(i)
    \/ Wait(i)
    \/ LeaveCS(i)
    \/ Exit(i)

Proc(i) == StartEntry(i) \/ Progress(i)

Next == \E i \in Procs : Proc(i)

Fairness == \A i \in Procs : WF_vars(Progress(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

(* Mutual exclusion: at most one process in the critical section *)
cs == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

MutualExclusion == cs

(* Absence of deadlock: if some process is trying, some process can step *)
Trying(i) == pc[i] \in {"setlevel", "setlast", "wait"}

DeadlockFree ==
    (\E i \in Procs : Trying(i)) => (\E i \in Procs : ENABLED Progress(i))

(* Starvation freedom: every trying process eventually enters the CS *)
StarvationFree == \A i \in Procs : Trying(i) ~> (pc[i] = "cs")

(* Some trying process eventually enters the CS *)
DeadlockFreedomLive ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

=============================================================================