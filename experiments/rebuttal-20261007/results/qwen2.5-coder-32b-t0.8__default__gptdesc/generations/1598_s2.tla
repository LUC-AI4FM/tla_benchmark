---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, S

Init == 
    /\ x = 1
    /\ y = 1
    /\ b = [i \in 1..N -> FALSE]
    /\ S = [i \in 1..N -> {}]

A(i) ==
    \/ /\ x = i
       /\ y # i
       /\ ~b[i]
    \/ /\ x # i
       /\ y = i
       /\ b[i]
       /\ S[i] = {}

C(i) ==
    /\ y = i
    /\ ~(\E j \in 1..N : j # i /\ b[j])

B(i) ==
    /\ x = i
    /\ y = i

Next == 
    \E i \in 1..N :
        \/ /\ A(i)
           /\ b' = [b EXCEPT ![i] = TRUE]
           /\ x' = i
           /\ S' = [S EXCEPT ![i] = {}]
           /\ UNCHANGED <<y>>
        \/ /\ C(i)
           /\ y' = (CHOOSE j \in {1..N} \ {i}: ~b[j])
           /\ b' = [b EXCEPT ![i] = FALSE]
           /\ S'' = [S' EXCEPT ![y'] = {}]
           /\ UNCHANGED <<x>>
        \/ /\ B(i)
           /\ y' = (LEAST j \in 1..N : ~b[j])
           /\ b' = [b EXCEPT ![i] = FALSE]
           /\ S'' = [S' EXCEPT ![y'] = {}]
           /\ UNCHANGED <<x>>
        \/ /\ x # i
           /\ y # i
           /\ ~b[i]
           /\ y' = (LEAST j \in 1..N : b[j])
           /\ S'' = [S' EXCEPT ![y'] = S[y'] \union {i}]
           /\ UNCHANGED <<x, b>>

Spec == 
    WF_next(Next) /\
    Init /\ [][Next]_<<x, y, b, S>> /\
    [](Cardinality({j \in 1..N : b[j]}) <= 1)

MutualExclusion == [](Cardinality({j \in 1..N : y = j}) <= 1)
Liveness == <>(\E i \in 1..N: y = i)

================================================================================