------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES flag, label1, label2

Init == 
    /\ flag = [i \in 1..N -> FALSE]
    /\ label1 = 0
    /\ label2 = 0

AcquireCS(i) ==
    \/ /\ flag[i] = TRUE
       /\ label1 = i
       /\ label2 = i
    \/ /\ flag[i] = FALSE
       /\ \E j \in 1..N : flag[j]
          -> \/ label1 # j
             \/ label2 # j

TryAcquire(i) ==
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ IF \A j \in 1..N \ {i} : ~flag[j] THEN
           /\ label1' = i
           /\ label2' = i
       ELSE
           /\ label1' = CHOOSE j \in 1..N : flag[j]
           /\ label2' = CHOOSE j \in 1..N : flag[j]

ReleaseCS(i) ==
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<label1, label2>>

Next ==
    \E i \in 1..N :
        \/ /\ ~AcquireCS(i)
           /\ TryAcquire(i)
        \/ /\ AcquireCS(i)
           /\ ReleaseCS(i)

Spec == 
    /\ Init
    /\ [][Next]_<<flag, label1, label2>>
    /\ WF_next(<<flag, label1, label2>>)

MutualExclusion ==
    \A i, j \in 1..N :
        i # j => ~(\E s \in StateTrace : flag[s][i] /\ flag[s][j])

Liveness ==
    \A i \in 1..N :
        WF_i(<<flag, label1, label2>>) =>
            \A S \in Seq(StateTrace) :
                \E k \in Nat : AcquireCS(i)[S[k]]

=============================================================================