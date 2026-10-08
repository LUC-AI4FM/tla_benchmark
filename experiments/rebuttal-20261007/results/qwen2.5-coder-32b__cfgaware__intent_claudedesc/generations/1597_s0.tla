------------------------------- MODULE FastMutex -------------------------------

CONSTANTS N \* Number of processes

VARIABLES x, y, b \* Shared variables and flag array

\* Process 1 (special process)
Process_1 == 
    /\ PC[1] = "try"
    /\ \/ /\ b[1]
           /\ x' = 1
           /\ y' = IF y = << >> THEN 1 ELSE y
           /\ b'[1] = FALSE
           /\ PC'[1] = "check"
       \/ /\ ~b[1]
           /\ b'[1] = TRUE
           /\ PC'[1] = "try"

\* Process i (i from 2 to N)
Process_i(i) == 
    /\ PC[i] \in {"try", "check"}
    /\ \/ /\ PC[i] = "try"
           /\ b[i]
           /\ x' = i
           /\ y' = IF y = << >> THEN i ELSE y
           /\ b'[i] = FALSE
           /\ PC'[i] = "check"
       \/ /\ PC[i] = "try"
           /\ ~b[i]
           /\ b'[i] = TRUE
           /\ PC'[i] = "try"

\* Critical section protocol for all processes
CriticalSection(i) ==
    /\ y # << >>
    /\ \A j \in 1..N : (j # i => ~b[j])
    /\ y' = << >>
    /\ b'[i] = TRUE
    /\ PC'[i] = "try"

\* Next state relation for all processes
Next ==
    \/ /\ PC[1] = "check"
       /\ CriticalSection(1)
    \/ \E i \in 2..N : 
           /\ PC[i] = "check"
           /\ CriticalSection(i)
    \/ Process_1
    \/ \E i \in 2..N : Process_i(i)

\* Initial predicate
Init ==
    /\ x = << >>
    /\ y = << >>
    /\ b = [j \in 1..N |-> FALSE]
    /\ PC = [j \in 1..N |-> "try"]

\* Invariant: Mutual exclusion in critical section
Invariant ==
    \/ y = << >>
    \/ \A i, j \in 1..N : (i # j => ~b[i] \/ ~b[j])

\* Liveness: Some process reaches the critical section infinitely often
Liveness ==
    <>[] (\E i \in 1..N : b[i])

\* Specification
Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b, PC>>
    /\ WF_[Next]_<<x, y, b, PC>>

===============================================================================