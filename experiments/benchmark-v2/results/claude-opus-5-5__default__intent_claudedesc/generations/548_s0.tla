------------------------------ MODULE PetersonN ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs  == 1..N
Levels == 1..(N-1)

VARIABLES
    pc,     \* pc[p] : program counter of process p
    level,  \* level[p] : highest level announced by process p (0 = not competing)
    last,   \* last[l] : the last process to enter level l (the "victim")
    cur     \* cur[p] : the level process p is currently working on

vars == << pc, level, last, cur >>

Labels == {"ncs", "loop", "setlast", "wait", "cs"}

TypeOK ==
    /\ pc    \in [Procs -> Labels]
    /\ level \in [Procs -> 0..(N-1)]
    /\ last  \in [Levels -> Procs]
    /\ cur   \in [Procs -> 1..N]

Init ==
    /\ pc    = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ last  = [l \in Levels |-> 1]
    /\ cur   = [p \in Procs |-> 1]

(* Non-critical section: the process decides to try to enter *)
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc'  = [pc  EXCEPT ![p] = "loop"]
    /\ cur' = [cur EXCEPT ![p] = 1]
    /\ UNCHANGED << level, last >>

(* Loop head: either announce the next level or enter the critical section *)
Loop(p) ==
    /\ pc[p] = "loop"
    /\ IF cur[p] <= N - 1
          THEN /\ level' = [level EXCEPT ![p] = cur[p]]
               /\ pc'    = [pc    EXCEPT ![p] = "setlast"]
          ELSE /\ pc'    = [pc    EXCEPT ![p] = "cs"]
               /\ UNCHANGED level
    /\ UNCHANGED << last, cur >>

(* Record that p is the last process to arrive at the current level *)
SetLast(p) ==
    /\ pc[p] = "setlast"
    /\ last' = [last EXCEPT ![cur[p]] = p]
    /\ pc'   = [pc   EXCEPT ![p] = "wait"]
    /\ UNCHANGED << level, cur >>

(* Wait until p is not the last at this level, or no other process
   is competing at this level or higher *)
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ last[cur[p]] # p
       \/ \A q \in Procs \ {p} : level[q] < cur[p]
    /\ cur' = [cur EXCEPT ![p] = cur[p] + 1]
    /\ pc'  = [pc  EXCEPT ![p] = "loop"]
    /\ UNCHANGED << level, last >>

(* Critical section followed by the exit protocol *)
Exit(p) ==
    /\ pc[p] = "cs"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ pc'    = [pc    EXCEPT ![p] = "ncs"]
    /\ UNCHANGED << last, cur >>

Proc(p) == NCS(p) \/ Loop(p) \/ SetLast(p) \/ Wait(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

(* Processes are not required to leave the non-critical section.
   All entry/exit steps are weakly fair; the waiting step is strongly
   fair since its enabling condition may be toggled by other processes. *)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(Loop(p))
        /\ WF_vars(SetLast(p))
        /\ SF_vars(Wait(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

InCS(p)   == pc[p] = "cs"
Trying(p) == pc[p] \in {"loop", "setlast", "wait"}

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

(* Liveness *)

DeadlockFreedom ==
    (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : InCS(p))

StarvationFreedom ==
    \A p \in Procs : Trying(p) ~> InCS(p)

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom
THEOREM Spec => StarvationFreedom
=============================================================================