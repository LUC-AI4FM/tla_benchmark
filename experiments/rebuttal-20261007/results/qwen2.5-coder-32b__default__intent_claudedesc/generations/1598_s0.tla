------------------------------- MODULE MutualExclusion -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b

ProcIds == 1..N

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [p \in ProcIds |-> FALSE]

TryEntry(p) ==
    /\ b' = [b EXCEPT ![p] = TRUE]
    /\ x' = p
    /\ y' = p

CheckContention(p) ==
    \/ y # p
    \/ (y = p /\ x # p)

BackOff(p) ==
    /\ b' = [b EXCEPT ![p] = FALSE]

WaitForClearY ==
    /\ UNCHANGED <<x, b>>
    /\ y' = 0

EnterCS(p) ==
    /\ UNCHANGED <<x, b>>

ExitCS(p) ==
    /\ y' = 0
    /\ b' = [b EXCEPT ![p] = FALSE]

ProcStep(p) ==
    \/ \E s \in {TryEntry, BackOff, WaitForClearY} : s(p)
    \/ EnterCS(p)
    \/ ExitCS(p)

Next ==
    \E p \in ProcIds :
        \/ /\ TryEntry(p)
           /\ ~CheckContention(p)
           /\ EnterCS(p)
        \/ /\ TryEntry(p)
           /\ CheckContention(p)
           /\ BackOff(p)
        \/ /\ b[p]
           /\ y = 0
           /\ WaitForClearY
        \/ /\ b[p]
           /\ y = p
           /\ x = p
           /\ EnterCS(p)
        \/ ExitCS(p)

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b>>
    /\ WF_<<x, y, b>>[ProcStep]

MutualExclusion ==
    \A p1, p2 \in ProcIds :
        \A s1, s2 \in Seq(<<x, y, b>>) :
            \/ s1 = s2
            \/ ~(\E i \in DOMAIN s1 : /\ s1[i] = EnterCS(p1) /\ s2[i] = EnterCS(p2))

Liveness ==
    \A p \in ProcIds : <<p>> \in Stable(EnterCS(p))

=============================================================================