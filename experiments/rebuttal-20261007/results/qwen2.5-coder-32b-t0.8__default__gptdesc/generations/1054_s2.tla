------------------------------ MODULE DijkstraTokenRing ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, M

VARIABLES values

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ N >= 1
       /\ M >= 1
       /\ N <= M + 1

Init == values \in [0..N-1 -> 0..M-1]

Next ==
    \/ /\ UNCHANGED values
       \/ \/ /\ \/ EX \E i \in {0} : values' = [values EXCEPT ![i] = (values[i] + 1) % M]
                  /\ \A j \in {1..N-1} : values'[j] = values[j]
          \/ \E i \in {1..N-1} : 
                /\ values'[i] = values[(i - 1) % N]
                /\ \A j \in (0..N-1) \ {i} : values'[j] = values[j]

Spec ==
    WF_vars(Next, <<values>>)
    /\ Spec_Once(Init, Next)

Stabilized ==
    \E i \in 0..N-1 :
        /\ values[i] # values[(i + 1) % N]
        /\ \A j \in (0..N-1) \ {i} : values[j] = values[(j + 1) % N]

Spec_Once ==
    Init
    /\ [][Next]_<<values>>
    /\ <><Stabilized>_<<values>>

=============================================================================