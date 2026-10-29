------------------------------ MODULE FilterMutex ------------------------------
(***************************************************************************)
(* N-process generalization of Peterson's algorithm (the Filter lock).    *)
(* There are N-1 ordered levels.  Each process records its current level  *)
(* in level[p], and last[k] records the last process to enter level k.    *)
(* A process at level k may advance only when it is no longer the last    *)
(* entrant at level k, or when no other process is at level k or higher.  *)
(* A process that clears level N-1 enters the critical section.           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs  == 1..N
Levels == 1..(N-1)

VARIABLES level, last, lvl, pc

vars == <<level, last, lvl, pc>>

EntryLabels == {"enter", "setLevel", "setLast", "wait"}
Labels      == {"ncs", "cs", "exit"} \cup EntryLabels

TypeOK ==
    /\ level \in [Procs -> 0..(N-1)]
    /\ last  \in [Levels -> Procs]
    /\ lvl   \in [Procs -> 1..N]
    /\ pc    \in [Procs -> Labels]

Init ==
    /\ level = [p \in Procs |-> 0]
    /\ last  = [k \in Levels |-> 1]
    /\ lvl   = [p \in Procs |-> 1]
    /\ pc    = [p \in Procs |-> "ncs"]

(* Noncritical section: a process may stay here forever (no fairness). *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED <<level, last, lvl>>

(* Begin the entry protocol at level 1. *)
enter(self) ==
    /\ pc[self] = "enter"
    /\ lvl' = [lvl EXCEPT ![self] = 1]
    /\ pc'  = [pc EXCEPT ![self] = IF N > 1 THEN "setLevel" ELSE "cs"]
    /\ UNCHANGED <<level, last>>

(* Announce the current level. *)
setLevel(self) ==
    /\ pc[self] = "setLevel"
    /\ level' = [level EXCEPT ![self] = lvl[self]]
    /\ pc'    = [pc EXCEPT ![self] = "setLast"]
    /\ UNCHANGED <<last, lvl>>

(* Record self as the last entrant at this level. *)
setLast(self) ==
    /\ pc[self] = "setLast"
    /\ last' = [last EXCEPT ![lvl[self]] = self]
    /\ pc'   = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<level, lvl>>

(* Spin until no conflict at this level, then advance. *)
wait(self) ==
    /\ pc[self] = "wait"
    /\ \/ last[lvl[self]] # self
       \/ \A k \in Procs \ {self} : level[k] < lvl[self]
    /\ lvl' = [lvl EXCEPT ![self] = lvl[self] + 1]
    /\ pc'  = [pc EXCEPT ![self] = IF lvl[self] + 1 < N THEN "setLevel" ELSE "cs"]
    /\ UNCHANGED <<level, last>>

(* Critical section. *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<level, last, lvl>>

(* Exit protocol: relinquish all levels. *)
exit(self) ==
    /\ pc[self] = "exit"
    /\ level' = [level EXCEPT ![self] = 0]
    /\ pc'    = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<last, lvl>>

proc(self) ==
    \/ ncs(self) \/ enter(self) \/ setLevel(self) \/ setLast(self)
    \/ wait(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : proc(self)

(* Fairness: every non-ncs step is weakly fair; the spin step is strongly *)
(* fair, since its enabling condition may be toggled by other processes. *)
Fairness ==
    \A self \in Procs :
        /\ WF_vars(enter(self))
        /\ WF_vars(setLevel(self))
        /\ WF_vars(setLast(self))
        /\ SF_vars(wait(self))
        /\ WF_vars(cs(self))
        /\ WF_vars(exit(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Absence of deadlock: if some process is contending, some process *)
(* eventually gets into the critical section.                       *)
DeadlockFreedom ==
    (\E p \in Procs : pc[p] \in EntryLabels) ~> (\E p \in Procs : pc[p] = "cs")

(* Starvation freedom: every process that tries eventually enters. *)
StarvationFreedom ==
    \A p \in Procs : (pc[p] \in EntryLabels) ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom
=============================================================================