---------------------------- MODULE PetersonN ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs == 1..N

Levels == 1..(N-1)

VARIABLES pc, level, last, lv

vars == << pc, level, last, lv >>

Labels == {"ncs", "setlevel", "setlast", "wait", "cs", "exit"}

TypeOK ==
  /\ pc \in [Procs -> Labels]
  /\ level \in [Procs -> 0..(N-1)]
  /\ last \in [Levels -> Procs]
  /\ lv \in [Procs -> 0..(N-1)]

Init ==
  /\ pc = [p \in Procs |-> "ncs"]
  /\ level = [p \in Procs |-> 0]
  /\ last = [l \in Levels |-> 1]
  /\ lv = [p \in Procs |-> 0]

(* Leave the non-critical section and start the entry protocol *)
NCS(p) ==
  /\ pc[p] = "ncs"
  /\ IF N > 1
       THEN /\ lv' = [lv EXCEPT ![p] = 1]
            /\ pc' = [pc EXCEPT ![p] = "setlevel"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
            /\ UNCHANGED lv
  /\ UNCHANGED << level, last >>

(* Announce the level reached *)
SetLevel(p) ==
  /\ pc[p] = "setlevel"
  /\ level' = [level EXCEPT ![p] = lv[p]]
  /\ pc' = [pc EXCEPT ![p] = "setlast"]
  /\ UNCHANGED << last, lv >>

(* Record self as last to arrive at this level *)
SetLast(p) ==
  /\ pc[p] = "setlast"
  /\ last' = [last EXCEPT ![lv[p]] = p]
  /\ pc' = [pc EXCEPT ![p] = "wait"]
  /\ UNCHANGED << level, lv >>

(* Wait until not last, or no other process at same or higher level *)
Wait(p) ==
  /\ pc[p] = "wait"
  /\ \/ last[lv[p]] # p
     \/ \A k \in Procs \ {p} : level[k] < lv[p]
  /\ IF lv[p] < N - 1
       THEN /\ lv' = [lv EXCEPT ![p] = lv[p] + 1]
            /\ pc' = [pc EXCEPT ![p] = "setlevel"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
            /\ UNCHANGED lv
  /\ UNCHANGED << level, last >>

(* Critical section *)
CS(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED << level, last, lv >>

(* Exit protocol *)
Exit(p) ==
  /\ pc[p] = "exit"
  /\ level' = [level EXCEPT ![p] = 0]
  /\ lv' = [lv EXCEPT ![p] = 0]
  /\ pc' = [pc EXCEPT ![p] = "ncs"]
  /\ UNCHANGED last

Proc(p) ==
  \/ NCS(p)
  \/ SetLevel(p)
  \/ SetLast(p)
  \/ Wait(p)
  \/ CS(p)
  \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness ==
  \A p \in Procs :
    /\ WF_vars(SetLevel(p))
    /\ WF_vars(SetLast(p))
    /\ SF_vars(Wait(p))
    /\ WF_vars(CS(p))
    /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

(* Mutual exclusion: at most one process in the critical section *)
cs == \A p, q \in Procs : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

MutualExclusion == cs

Trying(p) == pc[p] \in {"setlevel", "setlast", "wait"}

DeadlockFreedom ==
  (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : pc[p] = "cs")

StarvationFreedom ==
  \A p \in Procs : Trying(p) ~> (pc[p] = "cs")

=============================================================================