------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES x, y, b, pc

State == {0,1,2,3}   \* 0=outside,1=entry,2=cs,3=exit (unused)

vars == <<x, y, b, pc>>

Init ==
    /\ x = 0
    /\ y = 0
    /\ b \in [1..N -> BOOLEAN]
    /\ \A i \in 1..N : b[i] = FALSE
    /\ pc \in [1..N -> State]
    /\ \A i \in 1..N : pc[i] = 0

Entry1(i) ==
    /\ i \in 1..N
    /\ pc[i] = 0
    /\ b'[i] = TRUE
    /\ x' = i
    /\ pc'[i] = 1

Entry2(i) ==
    /\ i \in 1..N
    /\ pc[i] = 1
    /\ y = 0
    /\ y' = i
    /\ pc'[i] = 2

Exit(i) ==
    /\ i \in 1..N
    /\ pc[i] = 2
    /\ y' = 0
    /\ b'[i] = FALSE
    /\ pc'[i] = 0

Proc1Action ==
    \E i \in {1} :
        (Entry1(i) \/ Entry2(i) \/ Exit(i))

ProcOtherAction ==
    \E i \in 2..N :
        (Entry1(i) \/ Entry2(i) \/ Exit(i))

Next == Proc1Action \/ ProcOtherAction

MutualExclusion ==
    \A i, j \in 1..N : ((pc[i] = 2) /\ (pc[j] = 2)) => i = j

Liveness ==
    WF(Proc1Action) /\ WF(ProcOtherAction)

Spec == Init /\ [][Next]_vars /\ MutualExclusion /\ Liveness
=============================================================================