---------------------------- MODULE MCSession9peterson ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style mutual exclusion algorithm. *)
(* The original wrapper EXTENDS Session9peterson. That module was not      *)
(* available, so this file inlines an N-process Peterson (filter) algorithm*)
(* that uses the same locations ("enter", "cs") so that it parses alone.   *)
(* It then fixes concrete constants and states the two correctness         *)
(* properties: mutual exclusion and starvation freedom.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, P

\* Concrete values used for model checking (substitute in the .cfg file)
MC_N == 2
MC_P == 1 .. MC_N

ASSUME /\ N \in Nat
       /\ N >= 2
       /\ P = 1 .. N

VARIABLES pc, level, last, l

vars == << pc, level, last, l >>

Levels == 1 .. (N - 1)

TypeOK ==
    /\ pc \in [P -> {"ncs", "enter", "set", "wait", "cs"}]
    /\ level \in [P -> 0 .. (N - 1)]
    /\ last \in [Levels -> P]
    /\ l \in [P -> 0 .. (N - 1)]

Init ==
    /\ pc = [p \in P |-> "ncs"]
    /\ level = [p \in P |-> 0]
    /\ last = [k \in Levels |-> CHOOSE q \in P : TRUE]
    /\ l = [p \in P |-> 0]

\* Non-critical section: the process decides to try to enter
Try(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED << level, last, l >>

\* Begin the entry protocol at level 1
Enter(p) ==
    /\ pc[p] = "enter"
    /\ l' = [l EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "set"]
    /\ UNCHANGED << level, last >>

\* Announce the current level and yield priority at that level
SetLevel(p) ==
    /\ pc[p] = "set"
    /\ level' = [level EXCEPT ![p] = l[p]]
    /\ last' = [last EXCEPT ![l[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED l

\* Wait until no other process is at an equal or higher level,
\* or until another process has become the last one at this level
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A q \in P \ {p} : level[q] < l[p]
       \/ last[l[p]] # p
    /\ IF l[p] = N - 1
          THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED l
          ELSE /\ l' = [l EXCEPT ![p] = l[p] + 1]
               /\ pc' = [pc EXCEPT ![p] = "set"]
    /\ UNCHANGED << level, last >>

\* Leave the critical section
Exit(p) ==
    /\ pc[p] = "cs"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ l' = [l EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED last

Proc(p) ==
    \/ Try(p)
    \/ Enter(p)
    \/ SetLevel(p)
    \/ Wait(p)
    \/ Exit(p)

Next == \E p \in P : Proc(p)

\* Fairness: no fairness on Try (a process may stay in ncs forever).
\* The entry and exit steps are weakly fair, and the waiting step is
\* strongly fair because its guard can be enabled only intermittently.
Fairness ==
    \A p \in P :
        /\ WF_vars(Enter(p))
        /\ WF_vars(SetLevel(p))
        /\ SF_vars(Wait(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Safety: no two distinct processes are in the critical section at once
MutualExclusion ==
    \A p, q \in P : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: every process at location "enter" eventually reaches "cs"
StarvationFreedom ==
    \A p \in P : (pc[p] = "enter") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================