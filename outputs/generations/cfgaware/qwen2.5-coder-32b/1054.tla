------------------------------- MODULE TokenRing -------------------------------

CONSTANTS N, M

VARIABLES values

ASSUME N \in Nat /\ N >= 1
ASSUME M \in Nat /\ M >= 1
ASSUME N <= M + 1

Init == 
    /\ values \in [0..N-1 -> 0..M-1]
    /\ (\E i \in 0..N-1 : values[i] = 0)

Next ==
    \/ /\ PC = "CreateToken"
       /\ values[0] = (values[N-1] + 1) % M
       /\ UNCHANGED <<values[1..N-1]>>
    \/ /\ PC \in {"PassToken", "Stabilize"}
       /\ \E i \in 1..N-1 : 
            /\ values[i] # values[(i-1)%N]
            /\ values' = [values EXCEPT ![i] = values[(i-1)%N]]
            /\ UNCHANGED <<values[EXCEPT ![(i-1)%N]]>>

Spec == Init /\ [][Next]_<<values>>

Stabilized ==
    \E i \in 0..N-1 : 
        /\ values[i] = 0
        /\ \A j \in {k \in 0..N-1 : k # i} : values[j] # 0

THEOREM Spec => <>[](Stabilized)

=============================================================================