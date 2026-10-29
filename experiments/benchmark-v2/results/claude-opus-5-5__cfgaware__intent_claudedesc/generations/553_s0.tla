---------------------------- MODULE Peterson ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == 0 .. (ConstN - 1)

Levels == 1 .. (N - 1)

VARIABLES level, last, lvl, pc

vars == <<level, last, lvl, pc>>

TypeOK ==
    /\ level \in [Procs -> 0 .. (N - 1)]
    /\ last  \in [Levels -> Procs]
    /\ lvl   \in [Procs -> 0 .. N]
    /\ pc    \in [Procs -> {"ncs", "setlevel", "setlast", "wait", "cs", "exit"}]

Init ==
    /\ level = [p \in Procs |-> 0]
    /\ last  = [l \in Levels |-> CHOOSE p \in Procs : TRUE]
    /\ lvl   = [p \in Procs |-> 0]
    /\ pc    = [p \in Procs |-> "ncs"]

\* Leave the non-critical section and start the entry protocol
Try(p) ==
    /\ pc[p] = "ncs"
    /\ lvl' = [lvl EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = IF N > 1 THEN "setlevel" ELSE "cs"]
    /\ UNCHANGED <<level, last>>

\* level[p] := l
SetLevel(p) ==
    /\ pc[p] = "setlevel"
    /\ level' = [level EXCEPT ![p] = lvl[p]]
    /\ pc' = [pc EXCEPT ![p] = "setlast"]
    /\ UNCHANGED <<last, lvl>>

\* last[l] := p
SetLast(p) ==
    /\ pc[p] = "setlast"
    /\ last' = [last EXCEPT ![lvl[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<level, lvl>>

\* await (\A k # p : level[k] < l) \/ last[l] # p
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A k \in Procs \ {p} : level[k] < lvl[p]
       \/ last[lvl[p]] # p
    /\ IF lvl[p] < N - 1
          THEN /\ lvl' = [lvl EXCEPT ![p] = lvl[p] + 1]
               /\ pc' = [pc EXCEPT ![p] = "setlevel"]
          ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED lvl
    /\ UNCHANGED <<level, last>>

\* Leave the critical section
LeaveCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<level, last, lvl>>

\* Exit protocol: level[p] := 0
Exit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ lvl' = [lvl EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED last

Proc(p) ==
    \/ Try(p)
    \/ SetLevel(p)
    \/ SetLast(p)
    \/ Wait(p)
    \/ LeaveCS(p)
    \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(SetLevel(p))
        /\ WF_vars(SetLast(p))
        /\ SF_vars(Wait(p))
        /\ WF_vars(LeaveCS(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] \in {"setlevel", "setlast", "wait"}) ~> (pc[p] = "cs")

=============================================================================