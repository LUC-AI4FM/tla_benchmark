```tla
MODULE FastMutualExclusion

EXTENDS Naturals, Sequences, TLC

CONSTANTS N \* Number of processes

VARIABLES x, y, b \* Shared variables

Init == /\ x = 0 
        /\ y = 0 
        /\ b = <<FALSE>> ^ N

Next ==
    \/ /\ \/ \/ \/ \/ \/ \E i \in 1..N : 
              /\ x = 0
              /\ b' = [b EXCEPT ![i] = TRUE]
              /\ UNCHANGED <<x, y>>
         /\ \/ \/ /\ y' = i
                /\ UNCHANGED b
                /\ UNCHANGED x
            \/ /\ y # i
                /\ y' = y
                /\ UNCHANGED b
                /\ UNCHANGED x
    \/ /\ \/ \E i \in 1..N : 
              /\ x = 0
              /\ b[i]
              /\ (\A j \in 1..N \ {i} : ~b[j] \/ j = y)
              /\ x' = i
              /\ UNCHANGED <<y, b>>
    \/ /\ \/ \E i \in 1..N :
              /\ x = i
              /\ x' = 0
              /\ b' = [b EXCEPT ![i] = FALSE]
              /\ UNCHANGED y

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b>>
    /\ WF_x(<>)
    /\ WF_y(<>)
    /\ WF_b(<>)

MutualExclusion ==
    \A i, j \in 1..N : 
       \/ i = j
       \/ ~(\E k \in 1..N : x = k /\ y = i /\ b[j])

Liveness ==
    \A i \in 1..N :
        <>(\E k \in 1..N : x = k /\ y = i)

ConditionalLiveness ==
    \A i \in 1..N :
        [](b[i] => <>(x = i))

WF_x(st) == 
    WF_stutter(<>)

WF_y(st) == 
    WF_stutter(<>)

WF_b(st) == 
    WF_stutter(<>)

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
THEOREM Spec => ConditionalLiveness
```