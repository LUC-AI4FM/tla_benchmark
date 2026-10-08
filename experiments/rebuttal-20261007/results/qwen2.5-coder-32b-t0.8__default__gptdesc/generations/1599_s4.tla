---- MODULE FastMutualExclusion ----

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS N

VARIABLES x, y, b

Init == /\ x = 0
        /\ y = 1
        /\ b \in [1..N -> BOOLEAN]
        /\ \A i \in 1..N : b[i] = FALSE

Next ==
    \/ \E i \in 1..N :
         \* Request entry into critical section
         \/ /\ x = i
            /\ y = i
            /\ b[i]
            /\ x' = i
            /\ y' = i
            /\ b' = [b EXCEPT ![i] = FALSE]
         \/ /\ x = 0
            /\ \A j \in 1..N : ~b[j]
            /\ x' = i
            /\ y' = i
            /\ b' = [b EXCEPT ![i] = TRUE]
    \/ \E i \in 1..N :
         \* Compete for entry into critical section
         \/ /\ x = i
            /\ y = i
            /\ ~b[i]
            /\ x' = i
            /\ y' = (CHOOSE j \in 1..N : b[j] \/ j = y)
            /\ b' = [b EXCEPT ![i] = TRUE]
         \/ /\ x = i
            /\ y # i
            /\ ~b[i]
            /\ x' = y
            /\ y' = y
            /\ b' = b
    \/ \E i \in 1..N :
         \* In critical section
         \/ /\ x = i
            /\ y = i
            /\ ~b[i]
            /\ x' = i
            /\ y' = i
            /\ b' = b
    \/ \E i \in 1..N :
         \* Exit critical section
         \/ /\ x = i
            /\ y = i
            /\ ~b[i]
            /\ x' = 0
            /\ y' = y
            /\ b' = b

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b>>
    /\ WF_x(Next)

\* Mutual exclusion invariant
MutualExclusion == \A i,j \in 1..N : i # j => ~(x = i /\ y = i /\ x = j /\ y = j)

\* Liveness: Each process eventually enters the critical section
Liveness == \A i \in 1..N : <>(x = i /\ y = i /\ ~b[i])

\* Conditional liveness: If no process is in the critical section, some process must enter it
ConditionalLiveness ==
    [](~(\E i \in 1..N : x = i /\ y = i /\ ~b[i]) => <> (\E j \in 1..N : x' = j /\ y' = j))

\* Fairness-enhanced specification using weak fairness for each control-location action
FairSpec ==
    Spec
    /\ WF_x(Next)
    /\ SF_x(Next)

====