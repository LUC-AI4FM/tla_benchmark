---------------------------- MODULE MCSession9peterson ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, Procs

ASSUME NAssumption == N \in Nat /\ N >= 2
ASSUME ProcsAssumption == Procs = 1..N

Levels == 1..(N-1)

VARIABLES pc, level, victim, cur

vars == << pc, level, victim, cur >>

Locations == {"ncs", "enter", "setlevel", "setvictim", "wait", "cs"}

TypeOK ==
    /\ pc \in [Procs -> Locations]
    /\ level \in [Procs -> 0..(N-1)]
    /\ victim \in [Levels -> Procs]
    /\ cur \in [Procs -> 0..(N-1)]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ victim = [i \in Levels |-> CHOOSE q \in Procs : TRUE]
    /\ cur = [p \in Procs |-> 0]

Try(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED << level, victim, cur >>

Enter(p) ==
    /\ pc[p] = "enter"
    /\ cur' = [cur EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ UNCHANGED << level, victim >>

SetLevel(p) ==
    /\ pc[p] = "setlevel"
    /\ level' = [level EXCEPT ![p] = cur[p]]
    /\ pc' = [pc EXCEPT ![p] = "setvictim"]
    /\ UNCHANGED << victim, cur >>

SetVictim(p) ==
    /\ pc[p] = "setvictim"
    /\ victim' = [victim EXCEPT ![cur[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED << level, cur >>

Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A k \in Procs \ {p} : level[k] < cur[p]
       \/ victim[cur[p]] # p
    /\ IF cur[p] < N - 1
          THEN /\ cur' = [cur EXCEPT ![p] = cur[p] + 1]
               /\ pc' = [pc EXCEPT ![p] = "setlevel"]
          ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED cur
    /\ UNCHANGED << level, victim >>

Exit(p) ==
    /\ pc[p] = "cs"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ cur' = [cur EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED victim

Proc(p) ==
    \/ Enter(p)
    \/ SetLevel(p)
    \/ SetVictim(p)
    \/ Wait(p)
    \/ Exit(p)

Next == \E p \in Procs : Try(p) \/ Proc(p)

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: no two distinct processes are in the critical section simultaneously
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: any process at "enter" eventually reaches "cs"
StarvationFree ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => StarvationFree
====================================================================================