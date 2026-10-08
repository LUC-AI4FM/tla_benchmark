MODULE DijkstraTokenRing
EXTENDS Integers

CONSTANTS N, M

(* Assumptions: N >= 1 /\ M >= 1 /\ N <= M + 1 *)

VARIABLE X

Init == X \in [0..N-1 -> 0..M-1]

Next ==
    \E i \in 0..N-1 :
        IF i = 0 THEN
            /\ X[0] # ((X[N-1] + 1) MOD M)
            /\ X' = [X EXCEPT ![0] = ((X[N-1] + 1) MOD M)]
        ELSE
            /\ X[i] # X[i-1]
            /\ X' = [X EXCEPT ![i] = X[i-1]]

UniqueTokenStable ==
    \E i \in 0..N-1 :
        /\ X[i] # X[(i+1) MOD N]
        /\ \A j \in 0..N-1 : (j = i \/ X[j] = X[(j+1) MOD N])
        /\ X[i] = ((X[(i-1) MOD N] + 1) MOD M)

Liveness == \Box \Diamond UniqueTokenStable

Spec == Init /\ [][Next]_X /\ Liveness
=============================================================================