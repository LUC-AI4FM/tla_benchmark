------------------------------- MODULE FastMutualExclusion ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES x, y, b, j

Init == /\ x \in 1..N
        /\ y = 0
        /\ b \in [1..N -> BOOLEAN]
        /\ \A i \in 1..N : b[i] = FALSE
        /\ j \in [1..N -> {1,2}]
        /\ \A i \in 1..N : j[i] = 1

ProcessStep(i) == 
    \/ /\ j[i] = 1
       /\ (b[i]' = TRUE)
       /\ (j'[i] = 2)
    \/ /\ j[i] = 2
       /\ (\E k \in {1..N} \ {i} : b[k])
          /\ (y' = i)
          /\ (j'[i] = 3)
    \/ /\ j[i] = 2
       /\ ~(\E k \in {1..N} \ {i} : b[k])
          /\ (x' = i)
          /\ (b'[i] = FALSE)
          /\ (j'[i] = 4)
    \/ /\ j[i] = 3
       /\ x # i
       /\ (j'[i] = 1)
    \/ /\ j[i] = 3
       /\ y # i
       /\ x = i
       /\ (j'[i] = 5)
    \/ /\ j[i] = 4
       /\ (b'[x] = FALSE)
       /\ (j'[i] = 6)
    \/ /\ j[i] = 5
       /\ (y' = 0)
       /\ (j'[i] = 1)

Next == \E i \in 1..N : ProcessStep(i)

Spec == Init /\ [][Next]_<<ProcessStep(1), ..., ProcessStep(N)>> 
        /\ WF_[<<ProcessStep(1), ..., ProcessStep(N)>>]

MutualExclusion == \/ \A i, j \in 1..N \ {i} :
                       ~ (x = i) \/ ~ (b[j])
                     \/ x = 0

Liveness == <>[] (\E i \in 1..N : x = i)

THEOREM Spec => [] MutualExclusion
THEOREM Spec => Liveness

=============================================================================