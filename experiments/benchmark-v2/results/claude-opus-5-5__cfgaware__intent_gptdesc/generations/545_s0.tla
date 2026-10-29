------------------------------ MODULE FilterMutex ------------------------------
(***************************************************************************)
(* N-process mutual exclusion using Peterson's Filter algorithm.           *)
(* Each process passes through levels 1..N-1.  At level l it announces     *)
(* level[i] = l and makes itself victim[l].  It may advance past level l   *)
(* once no other process is at level >= l, or once some other process has  *)
(* become victim[l].  After level N-1 it enters the critical section.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == 1..ConstN

ASSUME /\ N \in Nat \ {0}
       /\ Procs \subseteq Nat \ {0}
       /\ Cardinality(Procs) = N

Levels == 1..(N-1)
NoProc == 0

VARIABLES pc, level, victim, lv

vars == <<pc, level, victim, lv>>

PCs == {"ncs", "set", "wait", "cs"}
Trying == {"set", "wait"}

TypeOK ==
  /\ pc \in [Procs -> PCs]
  /\ level \in [Procs -> 0..(N-1)]
  /\ victim \in [Levels -> Procs \cup {NoProc}]
  /\ lv \in [Procs -> 0..N]

Init ==
  /\ pc = [i \in Procs |-> "ncs"]
  /\ level = [i \in Procs |-> 0]
  /\ victim = [l \in Levels |-> NoProc]
  /\ lv = [i \in Procs |-> 0]

(* Leave noncritical section and start the entry protocol *)
Try(i) ==
  /\ pc[i] = "ncs"
  /\ lv' = [lv EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = IF N > 1 THEN "set" ELSE "cs"]
  /\ UNCHANGED <<level, victim>>

(* Announce current level and become the victim at that level *)
SetLevel(i) ==
  /\ pc[i] = "set"
  /\ level' = [level EXCEPT ![i] = lv[i]]
  /\ victim' = [victim EXCEPT ![lv[i]] = i]
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED lv

CanAdvance(i) ==
  \/ \A k \in Procs \ {i} : level[k] < lv[i]
  \/ victim[lv[i]] # i

(* Wait at the current level until allowed to proceed *)
Wait(i) ==
  /\ pc[i] = "wait"
  /\ CanAdvance(i)
  /\ IF lv[i] < N - 1
       THEN /\ lv' = [lv EXCEPT ![i] = lv[i] + 1]
            /\ pc' = [pc EXCEPT ![i] = "set"]
       ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
            /\ UNCHANGED lv
  /\ UNCHANGED <<level, victim>>

(* Leave the critical section and reset own level *)
Exit(i) ==
  /\ pc[i] = "cs"
  /\ level' = [level EXCEPT ![i] = 0]
  /\ lv' = [lv EXCEPT ![i] = 0]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED victim

Next == \E i \in Procs : Try(i) \/ SetLevel(i) \/ Wait(i) \/ Exit(i)

Fairness ==
  \A i \in Procs :
    /\ WF_vars(SetLevel(i))
    /\ SF_vars(Wait(i))
    /\ WF_vars(Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Safety *)
MutualExclusion ==
  \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

LevelConsistent ==
  \A i \in Procs :
    /\ (pc[i] = "ncs") => level[i] = 0
    /\ (pc[i] = "wait") => level[i] = lv[i]

VictimValid ==
  \A l \in Levels : victim[l] \in Procs \cup {NoProc}

Invariants == TypeOK /\ MutualExclusion /\ LevelConsistent /\ VictimValid

(* Liveness *)
StarvationFree ==
  \A i \in Procs : (pc[i] \in Trying) ~> (pc[i] = "cs")

DeadlockFree ==
  (\E i \in Procs : pc[i] \in Trying) ~> (\E j \in Procs : pc[j] = "cs")

EventuallyExit ==
  \A i \in Procs : (pc[i] = "cs") ~> (pc[i] = "ncs")

=============================================================================