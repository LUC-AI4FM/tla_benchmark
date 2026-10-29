------------------------------ MODULE Session8petersonMC ------------------------------
EXTENDS Naturals, FiniteSets

ConstN     == 3
ConstProcs == 0..(ConstN - 1)

N     == ConstN
Procs == ConstProcs

ASSUME N >= 2

Levels == 1..(N - 1)

VARIABLES pc, level, curr, last

vars == << pc, level, curr, last >>

PCs == {"ncs", "set", "wait", "cs"}

TypeOK ==
    /\ pc    \in [Procs -> PCs]
    /\ level \in [Procs -> 0..(N - 1)]
    /\ curr  \in [Procs -> 0..(N - 1)]
    /\ last  \in [Levels -> Procs]

Init ==
    /\ pc    = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ curr  = [p \in Procs |-> 0]
    /\ last  = [l \in Levels |-> CHOOSE p \in Procs : TRUE]

Request(i) ==
    /\ pc[i] = "ncs"
    /\ curr' = [curr EXCEPT ![i] = 1]
    /\ pc'   = [pc EXCEPT ![i] = "set"]
    /\ UNCHANGED << level, last >>

SetLevel(i) ==
    /\ pc[i] = "set"
    /\ level' = [level EXCEPT ![i] = curr[i]]
    /\ last'  = [last EXCEPT ![curr[i]] = i]
    /\ pc'    = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED curr

Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ last[curr[i]] # i
       \/ \A k \in Procs \ {i} : level[k] < curr[i]
    /\ IF curr[i] = N - 1
          THEN /\ pc'   = [pc EXCEPT ![i] = "cs"]
               /\ curr' = curr
          ELSE /\ curr' = [curr EXCEPT ![i] = curr[i] + 1]
               /\ pc'   = [pc EXCEPT ![i] = "set"]
    /\ UNCHANGED << level, last >>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ curr'  = [curr EXCEPT ![i] = 0]
    /\ pc'    = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED last

Proc(i) == Request(i) \/ SetLevel(i) \/ Wait(i) \/ Exit(i)

Next == \E i \in Procs : Proc(i)

Fairness ==
    \A i \in Procs : WF_vars(SetLevel(i) \/ Wait(i) \/ Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=======================================================================================