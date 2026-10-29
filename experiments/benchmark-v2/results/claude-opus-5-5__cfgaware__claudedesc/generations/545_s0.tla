---------------------------- MODULE Session8peterson_MC ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == {0, 1, 2}

VARIABLES pc, level, victim

vars == <<pc, level, victim>>

Levels == 1..(N - 1)

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "victim", "wait", "cs"}]
    /\ level \in [Procs -> 0..(N - 1)]
    /\ victim \in [Levels -> Procs]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ victim = [l \in Levels |-> CHOOSE q \in Procs : TRUE]

\* Process p leaves the non-critical section and enters level 1.
Try(p) ==
    /\ pc[p] = "ncs"
    /\ level' = [level EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "victim"]
    /\ UNCHANGED victim

\* Process p declares itself the victim at its current level.
SetVictim(p) ==
    /\ pc[p] = "victim"
    /\ victim' = [victim EXCEPT ![level[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED level

\* Process p waits until no other process is at its level or higher,
\* or until it is no longer the victim at its level.
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A k \in Procs \ {p} : level[k] < level[p]
       \/ victim[level[p]] # p
    /\ IF level[p] = N - 1
          THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED level
          ELSE /\ level' = [level EXCEPT ![p] = level[p] + 1]
               /\ pc' = [pc EXCEPT ![p] = "victim"]
    /\ UNCHANGED victim

\* Process p leaves the critical section.
Exit(p) ==
    /\ pc[p] = "cs"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED victim

Proc(p) == Try(p) \/ SetVictim(p) \/ Wait(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(Proc(p))

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================