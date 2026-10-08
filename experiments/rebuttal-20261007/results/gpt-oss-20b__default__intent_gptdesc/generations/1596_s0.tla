MODULE FastMutex
EXTENDS Naturals

CONSTANT N

VARIABLES procState, flag

Init ==
    /\ procState = [i \in 1..N |-> "idle"]
    /\ flag     = [i \in 1..N |-> FALSE]

Attempt(i) ==
    /\ i \in 1..N
    /\ procState[i] = "idle"
    /\ flag[i]      = FALSE
    /\ procState'   = [procState EXCEPT ![i] = "wait"]
    /\ flag'        = [flag EXCEPT ![i] = TRUE]

Abort(i) ==
    /\ i \in 1..N
    /\ procState[i] = "wait"
    /\ EXISTS j \in 1..N \ {i} : flag[j] = TRUE
    /\ procState'   = [procState EXCEPT ![i] = "idle"]
    /\ flag'        = [flag EXCEPT ![i] = FALSE]

EnterCS(i) ==
    /\ i \in 1..N
    /\ procState[i] = "wait"
    /\ ~(\E j \in 1..N \ {i} : flag[j] = TRUE)
    /\ procState'   = [procState EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<flag>>

ExitCS(i) ==
    /\ i \in 1..N
    /\ procState[i] = "cs"
    /\ procState'   = [procState EXCEPT ![i] = "idle"]
    /\ flag'        = [flag EXCEPT ![i] = FALSE]

Next == \E i \in 1..N : Attempt(i) \/ Abort(i) \/ EnterCS(i) \/ ExitCS(i)

AttemptAll == \E i \in 1..N : Attempt(i)
EnterCSAll == \E i \in 1..N : EnterCS(i)

MutualExclusion ==
    \A i, j \in 1..N :
        (i # j) => ~(procState[i] = "cs" /\ procState[j] = "cs")

GlobalEntryFairness ==
    []<> (\E i \in 1..N : procState[i] = "cs")

PerProcessLiveness ==
    \A i \in 1..N :
        [] (procState[i] = "idle" => <> (procState[i] = "cs"))

Spec == Init /\ [][Next]_<<procState, flag>> /\ WF_action(AttemptAll) /\ WF_action(EnterCSAll)