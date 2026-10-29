---------------------------- MODULE PetersonMutex ----------------------------
(***************************************************************************)
(* Peterson's filter algorithm: mutual exclusion for N processes.          *)
(*                                                                         *)
(* Each process i climbs through levels 1 .. N-1.  At level l it          *)
(* announces level[i] = l and makes itself the victim of level l.  It      *)
(* then waits until no other process is at level l or higher, or until     *)
(* another process has become the victim of level l.  A process that      *)
(* passes level N-1 enters the critical section.  On exit it resets        *)
(* level[i] to 0.                                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == 0 .. (ConstN - 1)

ASSUME N \in Nat /\ N >= 1
ASSUME IsFiniteSet(Procs) /\ Procs # {}

Levels == 1 .. (N - 1)

VARIABLES
    pc,      \* program counter of each process
    level,   \* level[i]: level currently announced by process i (0 = idle)
    victim,  \* victim[l]: last process to arrive at level l
    lv       \* lv[i]: loop variable, the level process i is working on

vars == << pc, level, victim, lv >>

PCs == {"ncs", "setlevel", "setvictim", "wait", "cs"}

TypeOK ==
    /\ pc \in [Procs -> PCs]
    /\ level \in [Procs -> 0 .. (N - 1)]
    /\ victim \in [Levels -> Procs]
    /\ lv \in [Procs -> 0 .. (N - 1)]

Init ==
    /\ pc = [i \in Procs |-> "ncs"]
    /\ level = [i \in Procs |-> 0]
    /\ victim = [l \in Levels |-> CHOOSE p \in Procs : TRUE]
    /\ lv = [i \in Procs |-> 0]

\* Process i requests entry to the critical section.
Request(i) ==
    /\ pc[i] = "ncs"
    /\ IF N > 1
         THEN /\ lv' = [lv EXCEPT ![i] = 1]
              /\ pc' = [pc EXCEPT ![i] = "setlevel"]
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED lv
    /\ UNCHANGED << level, victim >>

\* level[i] := l
SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ level' = [level EXCEPT ![i] = lv[i]]
    /\ pc' = [pc EXCEPT ![i] = "setvictim"]
    /\ UNCHANGED << victim, lv >>

\* victim[l] := i
SetVictim(i) ==
    /\ pc[i] = "setvictim"
    /\ victim' = [victim EXCEPT ![lv[i]] = i]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED << level, lv >>

\* wait while (\E k # i : level[k] >= l) /\ victim[l] = i
CanProceed(i) ==
    \/ \A k \in Procs \ {i} : level[k] < lv[i]
    \/ victim[lv[i]] # i

Wait(i) ==
    /\ pc[i] = "wait"
    /\ CanProceed(i)
    /\ IF lv[i] < N - 1
         THEN /\ lv' = [lv EXCEPT ![i] = lv[i] + 1]
              /\ pc' = [pc EXCEPT ![i] = "setlevel"]
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED lv
    /\ UNCHANGED << level, victim >>

\* Leave the critical section.
Exit(i) ==
    /\ pc[i] = "cs"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ lv' = [lv EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED victim

Proc(i) ==
    \/ Request(i)
    \/ SetLevel(i)
    \/ SetVictim(i)
    \/ Wait(i)
    \/ Exit(i)

Next == \E i \in Procs : Proc(i)

Fairness ==
    \A i \in Procs :
        /\ WF_vars(SetLevel(i))
        /\ WF_vars(SetVictim(i))
        /\ SF_vars(Wait(i))
        /\ WF_vars(Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in {"setlevel", "setvictim", "wait"}

DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E j \in Procs : pc[j] = "cs")

StarvationFreedom ==
    \A i \in Procs : Trying(i) ~> (pc[i] = "cs")

=============================================================================