---------------------------- MODULE MCPeterson ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == {0, 1, 2}

VARIABLES pc, level, last, lv

vars == <<pc, level, last, lv>>

Levels == 1..(N-1)

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "enter", "setlevel", "wait", "cs"}]
    /\ level \in [Procs -> 0..(N-1)]
    /\ last \in [Levels -> Procs]
    /\ lv \in [Procs -> 0..(N-1)]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ last = [l \in Levels |-> CHOOSE p \in Procs : TRUE]
    /\ lv = [p \in Procs |-> 0]

NCS(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "enter"]
    /\ UNCHANGED <<level, last, lv>>

Enter(i) ==
    /\ pc[i] = "enter"
    /\ IF N > 1
         THEN /\ lv' = [lv EXCEPT ![i] = 1]
              /\ pc' = [pc EXCEPT ![i] = "setlevel"]
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED lv
    /\ UNCHANGED <<level, last>>

SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ level' = [level EXCEPT ![i] = lv[i]]
    /\ last' = [last EXCEPT ![lv[i]] = i]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED lv

Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ \A k \in Procs \ {i} : level[k] < lv[i]
       \/ last[lv[i]] # i
    /\ IF lv[i] < N - 1
         THEN /\ lv' = [lv EXCEPT ![i] = lv[i] + 1]
              /\ pc' = [pc EXCEPT ![i] = "setlevel"]
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED lv
    /\ UNCHANGED <<level, last>>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ lv' = [lv EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED last

Proc(i) == Enter(i) \/ SetLevel(i) \/ Wait(i) \/ Exit(i)

Next == \E i \in Procs : NCS(i) \/ Proc(i)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i \in Procs : WF_vars(Enter(i) \/ SetLevel(i) \/ Exit(i))
        /\ \A i \in Procs : SF_vars(Wait(i))

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

StarvationFree ==
    \A i \in Procs : (pc[i] = "enter") ~> (pc[i] = "cs")

=============================================================================