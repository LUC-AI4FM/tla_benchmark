------------------------------- MODULE FastMutex -------------------------------

CONSTANTS N \* Number of processes

VARIABLES 
    flag,  \* Array of boolean flags indicating interest in entering critical section
    turn1, \* First shared register for process identity
    turn2  \* Second shared register for process identity

\* Initial predicate
Init == /\ flag = [i \in 1..N -> FALSE]
        /\ turn1 = 0
        /\ turn2 = 0

\* Process i announces its interest in entering the critical section
Announce(i) == 
    /\ flag' = [flag EXCEPT ![i] = TRUE]

\* Process i writes its identity into the shared registers
WriteTurns(i) ==
    /\ turn1' = i
    /\ turn2' = i

\* Process i checks for contention and waits if necessary
CheckAndWait(i) ==
    \/ /\ turn1 # i
       /\ turn2 # i
    \/ /\ turn1 = i
       /\ \E j \in 1..N : flag[j] /\ j # i /\ turn2 = j

\* Process i clears the shared state it set and resets its flag
ClearState(i) ==
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ turn1' = IF turn1 = i THEN 0 ELSE turn1
    /\ turn2' = IF turn2 = i THEN 0 ELSE turn2

\* Process i's actions to enter the critical section
AcquireLock(i) ==
    Announce(i)
    \/ CheckAndWait(i)
    \/ WriteTurns(i)

\* Process i's actions in the non-critical section
NonCriticalSection(i) == SKIP

\* Process i's actions to leave the critical section
ReleaseLock(i) ==
    ClearState(i)

\* Process i's complete cycle of actions
ProcessCycle(i) ==
    \/ /\ NonCriticalSection(i)
       /\ UNCHANGED <<flag, turn1, turn2>>
    \/ /\ AcquireLock(i)
       /\ ReleaseLock(i)

\* Specification for all processes
Spec == 
    Init
    /\ [][\A i \in 1..N : ProcessCycle(i)]_<<flag, turn1, turn2>>

\* Mutual exclusion invariant: no two distinct processes in critical section simultaneously
Invariant ==
    \/ turn1 = 0
    \/ turn2 = 0
    \/ \A i, j \in 1..N : i # j => ~flag[i] \/ ~flag[j]

\* Conditional liveness property: if some process is continuously attempting to enter,
\* then some process must enter the critical section infinitely often.
CondLiveness ==
    [](\/ i \in 1..N : flag[i]) => <>(turn1 # 0 /\ turn2 # 0)

\* Fair specification with weak fairness for every protocol step for every process
FairSpec ==
    Spec
    /\ WF_<<flag, turn1, turn2>>(ProcessCycle)

=============================================================================