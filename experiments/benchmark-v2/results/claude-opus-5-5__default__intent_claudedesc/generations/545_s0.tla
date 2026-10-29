---------------------------- MODULE PetersonFilter ----------------------------
(***************************************************************************)
(* Peterson's mutual exclusion algorithm generalized to N processes        *)
(* (the "filter lock").                                                    *)
(*                                                                         *)
(* Each process climbs N-1 levels. At level l, process i:                  *)
(*   1. sets level[i] := l                                                 *)
(*   2. sets victim[l] := i                                                *)
(*   3. waits while (\E k # i : level[k] >= l) /\ victim[l] = i            *)
(* After passing level N-1 it enters the critical section. On exit it      *)
(* resets level[i] := 0.                                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs  == 0 .. (N - 1)
Levels == 1 .. (N - 1)

VARIABLES
    pc,      \* program counter of each process
    level,   \* level[i] : the level process i has announced (0 = not competing)
    victim,  \* victim[l] : the last process to arrive at level l
    lvl      \* lvl[i] : the level process i is currently working on

vars == <<pc, level, victim, lvl>>

PCs == {"ncs", "setLevel", "setVictim", "wait", "cs"}

TypeOK ==
    /\ pc     \in [Procs -> PCs]
    /\ level  \in [Procs -> 0 .. (N - 1)]
    /\ victim \in [Levels -> Procs]
    /\ lvl    \in [Procs -> 0 .. N]

Init ==
    /\ pc     = [i \in Procs  |-> "ncs"]
    /\ level  = [i \in Procs  |-> 0]
    /\ victim = [l \in Levels |-> 0]
    /\ lvl    = [i \in Procs  |-> 0]

(* Process i decides to request the critical section. *)
Request(i) ==
    /\ pc[i] = "ncs"
    /\ pc'  = [pc  EXCEPT ![i] = "setLevel"]
    /\ lvl' = [lvl EXCEPT ![i] = 1]
    /\ UNCHANGED <<level, victim>>

(* Announce the current level, or enter the CS if all levels are passed. *)
SetLevel(i) ==
    /\ pc[i] = "setLevel"
    /\ IF lvl[i] <= N - 1
         THEN /\ level' = [level EXCEPT ![i] = lvl[i]]
              /\ pc'    = [pc    EXCEPT ![i] = "setVictim"]
         ELSE /\ pc'    = [pc    EXCEPT ![i] = "cs"]
              /\ UNCHANGED level
    /\ UNCHANGED <<victim, lvl>>

(* Declare oneself the victim at the current level. *)
SetVictim(i) ==
    /\ pc[i] = "setVictim"
    /\ victim' = [victim EXCEPT ![lvl[i]] = i]
    /\ pc'     = [pc     EXCEPT ![i] = "wait"]
    /\ UNCHANGED <<level, lvl>>

(* Wait until no other process is at this level or above, or until *)
(* another process has become the victim at this level.            *)
Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ \A k \in Procs \ {i} : level[k] < lvl[i]
       \/ victim[lvl[i]] # i
    /\ lvl' = [lvl EXCEPT ![i] = lvl[i] + 1]
    /\ pc'  = [pc  EXCEPT ![i] = "setLevel"]
    /\ UNCHANGED <<level, victim>>

(* Leave the critical section. *)
Exit(i) ==
    /\ pc[i] = "cs"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ lvl'   = [lvl   EXCEPT ![i] = 0]
    /\ pc'    = [pc    EXCEPT ![i] = "ncs"]
    /\ UNCHANGED victim

Proc(i) ==
    \/ Request(i)
    \/ SetLevel(i)
    \/ SetVictim(i)
    \/ Wait(i)
    \/ Exit(i)

Next == \E i \in Procs : Proc(i)

(* Fairness: a process is never forced to request the CS, but once it  *)
(* is competing or in the CS it keeps taking steps.                    *)
Fairness ==
    \A i \in Procs :
        /\ WF_vars(SetLevel(i))
        /\ WF_vars(SetVictim(i))
        /\ SF_vars(Wait(i))
        /\ WF_vars(Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in {"setLevel", "setVictim", "wait"}

-----------------------------------------------------------------------------
(* Liveness *)

(* If some process is trying, some process eventually enters the CS. *)
DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

(* Every process that requests the CS eventually enters it. *)
StarvationFreedom ==
    \A i \in Procs : Trying(i) ~> (pc[i] = "cs")

(* A process in the CS eventually leaves it. *)
EventuallyExits ==
    \A i \in Procs : (pc[i] = "cs") ~> (pc[i] = "ncs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom /\ EventuallyExits
=============================================================================