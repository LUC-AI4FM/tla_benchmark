----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals, TLC

CONSTANT N \* number of processes

VARIABLES x, y, b, S, pc

vars == <<x, y, b, S, pc>>

StateStart == "Start"
StateTryCS  == "TryCS"
StateInCS   == "InCS"

Init ==
    /\ x = 0
    /\ y = 0
    /\ b \in [1..N -> BOOLEAN]
    /\ S = {}
    /\ pc \in [1..N -> {"Start","TryCS","InCS"}]
    /\ \A i \in 1..N : b[i] = FALSE /\ pc[i] = StateStart

StartAction(i) ==
    /\ pc[i] = StateStart
    /\ b'   = [b EXCEPT ![i] = TRUE]
    /\ x'   = i
    /\ S'   = S \cup {i}
    /\ pc'[i] = StateTryCS

TryCSAction(i) ==
    /\ pc[i] = StateTryCS
    /\ y = i
    /\ pc'[i] = StateInCS
    /\ S'     = S \ {i}

RetryAction(i) ==
    /\ pc[i] = StateTryCS
    /\ y # i
    /\ b'[i] = FALSE
    /\ pc'[i] = StateStart
    /\ S'     = S \ {i}

ExitAction(i) ==
    /\ pc[i] = StateInCS
    /\ b'[i] = FALSE
    /\ y'   = i
    /\ pc'[i] = StateStart
    /\ S'   = S \ {i}

Next ==
    \E i \in 1..N :
        \/ StartAction(i)
        \/ TryCSAction(i)
        \/ RetryAction(i)
        \/ ExitAction(i)

MutualExclusion ==
    \A i, j \in 1..N : (i /= j) => ~(pc[i] = StateInCS /\ pc[j] = StateInCS)

LivenessProp ==
    []<>(\E i \in 1..N : pc[i] = StateInCS)

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ MutualExclusion

=============================================================================