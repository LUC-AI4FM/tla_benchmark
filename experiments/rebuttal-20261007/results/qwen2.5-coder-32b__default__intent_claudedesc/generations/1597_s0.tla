------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N >= 2

VARIABLES x, y, b

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N -> FALSE]

Next ==
    \/ \/ /\ x = 0
          /\ y = 0
          /\ b[1] = FALSE
          /\ \/ /\ b' = [b EXCEPT ![1] = TRUE]
             /\ x' = 1
             /\ y' = 1
       \/ /\ \E i \in 2..N : b[i]
          /\ \/ /\ b' = [b EXCEPT ![i] = FALSE]
             /\ x' = 0
             /\ y' = 0
    \/ \/ /\ b[1]
          /\ x = 1
          /\ y = 1
          /\ \/ /\ \A i \in 2..N : ~b[i]
                /\ b' = [b EXCEPT ![1] = FALSE]
                /\ x' = 0
                /\ y' = 0
             /\ \/ /\ \E i \in 2..N : b[i]
                    /\ b' = [b EXCEPT ![1] = FALSE]
                    /\ x' = 0
                    /\ y' = 0
    \/ \/ /\ \A i \in 2..N : ~b[i]
          /\ \/ /\ \E j \in 2..N : 
                \/ /\ b[j]
                   /\ b' = [b EXCEPT ![j] = FALSE]
                   /\ x' = 0
                   /\ y' = 0
             /\ \/ /\ \A j \in 2..N : ~b[j]
                    /\ \/ /\ b[1]
                          /\ b' = [b EXCEPT ![1] = FALSE]
                          /\ x' = 0
                          /\ y' = 0
                       /\ \/ /\ \E k \in 2..N :
                             \/ /\ b[k]
                                /\ b' = [b EXCEPT ![k] = FALSE]
                                /\ x' = 0
                                /\ y' = 0
                        /\ \/ /\ \A k \in 2..N : ~b[k]
                              /\ b' = [b EXCEPT ![1] = TRUE]
                              /\ x' = 1
                              /\ y' = 1
    \/ \/ /\ i \in 2..N
          /\ b[i] = FALSE
          /\ x = 0
          /\ y = 0
          /\ \/ /\ b' = [b EXCEPT ![i] = TRUE]
             /\ x' = i
             /\ y' = i
       \/ /\ \E j \in 1..N : j # i /\ b[j]
          /\ \/ /\ b' = [b EXCEPT ![i] = FALSE]
             /\ x' = 0
             /\ y' = 0
    \/ \/ /\ i \in 2..N
          /\ b[i]
          /\ x = i
          /\ y = i
          /\ \/ /\ \A j \in 1..N : j # i => ~b[j]
                /\ b' = [b EXCEPT ![i] = FALSE]
                /\ x' = 0
                /\ y' = 0
             /\ \/ /\ \E j \in 1..N : j # i /\ b[j]
                    /\ b' = [b EXCEPT ![i] = FALSE]
                    /\ x' = 0
                    /\ y' = 0

Spec ==
    WF_vars(Next, <<x, y, b>>) /\
    Init /\ [][Next]_<<x, y, b>> /\
    [](\/ i \in 1..N : ~b[i]) /\
    [](\/ i \in 1..N : \/ b[i] => (x = i) /\ (y = i))

=============================================================================