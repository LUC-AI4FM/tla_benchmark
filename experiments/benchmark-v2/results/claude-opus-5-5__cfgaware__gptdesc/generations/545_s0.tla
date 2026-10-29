---------------------------- MODULE MC_Session8peterson ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style (filter lock) mutual         *)
(* exclusion protocol for N processes. The protocol is defined inline       *)
(* (in place of the external Session8peterson module) and is checked       *)
(* with the concrete constants ConstN = 3 and ConstProcs = 0..(ConstN-1).  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

VARIABLES pc, level, last, l

vars == << pc, level, last, l >>

\* Concrete constants used by the model-checking configuration
ConstN == 3
ConstProcs == 0..(ConstN - 1)

Levels == 1..(N - 1)

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "set", "wait", "cs"}]
    /\ level \in [Procs -> 0..(N - 1)]
    /\ last \in [Levels -> Procs]
    /\ l \in [Procs -> 0..(N - 1)]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ last = [i \in Levels |-> CHOOSE q \in Procs : TRUE]
    /\ l = [p \in Procs |-> 0]

\* Leave the non-critical section and start climbing the levels
Start(p) ==
    /\ pc[p] = "ncs"
    /\ IF N > 1
         THEN /\ l' = [l EXCEPT ![p] = 1]
              /\ pc' = [pc EXCEPT ![p] = "set"]
         ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED l
    /\ UNCHANGED << level, last >>

\* Announce the intention to enter level l[p] and become its victim
SetLevel(p) ==
    /\ pc[p] = "set"
    /\ level' = [level EXCEPT ![p] = l[p]]
    /\ last' = [last EXCEPT ![l[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED l

\* Wait until no other process is at an equal or higher level,
\* or someone else has become the victim at this level
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A k \in Procs \ {p} : level[k] < l[p]
       \/ last[l[p]] # p
    /\ IF l[p] < N - 1
         THEN /\ l' = [l EXCEPT ![p] = l[p] + 1]
              /\ pc' = [pc EXCEPT ![p] = "set"]
         ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED l
    /\ UNCHANGED << level, last >>

\* Leave the critical section
Exit(p) ==
    /\ pc[p] = "cs"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ l' = [l EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED last

Proc(p) == Start(p) \/ SetLevel(p) \/ Wait(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs :
              /\ WF_vars(SetLevel(p))
              /\ WF_vars(Wait(p))
              /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety property: no two distinct processes are in the critical section
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================