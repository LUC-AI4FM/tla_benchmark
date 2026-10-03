------------------------------ MODULE DijkstraRing ------------------------------
EXTENDS Naturals, Integers

CONSTANTS N, M

ConstantsAssumptions ==
    /\ N >= 1
    /\ M >= 1
    /\ N <= M + 1

VARIABLE c

TypeInvariant == c \in [0 .. N-1 -> 0 .. M-1]

Init == TypeInvariant /\ ConstantsAssumptions

Node0Action ==
    /\ c[0] #= Mod(c[N-1] + 1, M)
    /\ c' = [c EXCEPT ![0] = Mod(c[N-1] + 1, M)]

NodeAction(i) ==
    /\ i \in 1 .. N-1
    /\ c[i] #= c[i-1]
    /\ c' = [c EXCEPT ![i] = c[i-1]]

Next == Node0Action \/ \E i \in 1 .. N-1 : NodeAction(i)

Spec == Init /\ [][Next]_c

UniqueToken ==
    \E i \in 0 .. N-1 :
        /\ \A j, k \in 0 .. N-1 :
            ((j <> i) /\ (k <> i)) => c[j] = c[k]
        /\ \A j \in 0 .. N-1 : (j <> i) => c[j] #= c[i]

THEOREM Stabilization ==
    Spec => <>[]UniqueToken

END MODULE