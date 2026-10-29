---------------------------- MODULE MCSession9peterson ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

VARIABLES pc, level, victim, lv

vars == <<pc, level, victim, lv>>

ConstN == 2
ConstProcs == 1..2

Locations == {"ncs", "enter", "setlevel", "wait", "cs", "exit"}

TypeOK ==
    /\ pc \in [Procs -> Locations]
    /\ level \in [Procs -> 0..N]
    /\ victim \in [1..N -> Procs]
    /\ lv \in [Procs -> 0..N]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ victim = [k \in 1..N |-> CHOOSE q \in Procs : TRUE]
    /\ lv = [p \in Procs |-> 0]

NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED <<level, victim, lv>>

Enter(p) ==
    /\ pc[p] = "enter"
    /\ lv' = [lv EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ UNCHANGED <<level, victim>>

SetLevel(p) ==
    /\ pc[p] = "setlevel"
    /\ IF lv[p] < N
          THEN /\ level' = [level EXCEPT ![p] = lv[p]]
               /\ victim' = [victim EXCEPT ![lv[p]] = p]
               /\ pc' = [pc EXCEPT ![p] = "wait"]
          ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED <<level, victim>>
    /\ UNCHANGED lv

Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A k \in Procs \ {p} : level[k] < lv[p]
       \/ victim[lv[p]] # p
    /\ lv' = [lv EXCEPT ![p] = lv[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ UNCHANGED <<level, victim>>

CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<level, victim, lv>>

Exit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ lv' = [lv EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED victim

Step(p) == Enter(p) \/ SetLevel(p) \/ Wait(p) \/ CS(p) \/ Exit(p)

Next == \E p \in Procs : NCS(p) \/ Step(p)

Fairness == \A p \in Procs : SF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

=============================================================================