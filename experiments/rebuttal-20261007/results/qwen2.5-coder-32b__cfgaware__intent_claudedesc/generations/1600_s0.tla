------------------------------- MODULE FastMutex -------------------------------

CONSTANTS N \* Number of processes

VARIABLES 
    turn,  \* Shared variable indicating interest
    flag,  \* Array of flags for each process
    cs     \* Critical section occupancy indicator (1 if occupied, 0 otherwise)

\* Initial state: No process is in the critical section, no interests are announced, and all flags are clear.
defaultInitValue == <<0, [i \in 1..N |-> FALSE], 0>>

Init == 
    /\ turn = 0
    /\ flag = [i \in 1..N |-> FALSE]
    /\ cs = 0

\* Process i attempts to enter the critical section.
TryEnterCS(i) ==
    /\ turn' = i
    /\ flag[i]' = TRUE

\* Process i checks if it can proceed directly or must wait.
CheckProceed(i) ==
    \/ /\ turn = i
       /\ \A j \in 1..N \ {i}: ~flag[j]
    \/ /\ turn = i
       /\ \E j \in 1..N \ {i}: flag[j]

\* Process i clears its flag and waits for all other flags to be clear.
WaitForFlags(i) ==
    /\ flag[i]' = FALSE
    /\ \A j \in 1..N \ {i}: ~flag[j] -> Skip

\* Process i checks if it still holds the turn variable; if not, it waits until turn is zero.
CheckTurn(i) ==
    \/ turn = i
    \/ /\ turn # i
       /\ turn' = 0

\* Process i enters the critical section.
EnterCS(i) ==
    /\ cs' = 1

\* Process i exits the critical section and clears its state.
ExitCS(i) ==
    /\ cs' = 0
    /\ flag[i]' = FALSE
    /\ turn' = 0

\* The behavior of a single process.
ProcessBehavior(i) ==
    \E j \in 1..N: 
        \/ /\ TryEnterCS(i)
           /\ CheckProceed(i)
           /\ WaitForFlags(i)
           /\ CheckTurn(i)
           /\ EnterCS(i)
        \/ /\ ~CheckProceed(i)
           /\ Skip
        \/ ExitCS(i)

\* The complete specification for all processes.
Spec == Init /\ [][\A i \in 1..N: ProcessBehavior(i)]_<<turn, flag, cs>>

\* Invariant: Mutual exclusion (only one process can be in the critical section at a time).
Invariant ==
    \/ cs = 0
    \/ \E i \in 1..N: /\ cs = 1
                       /\ turn = i
                       /\ flag[i]

\* Liveness: Some process must infinitely often succeed in entering the critical section.
Liveness ==
    <>[](\E i \in 1..N: <>(turn = i) /\ (flag[i]) /\ (cs = 1))

=============================================================================