---------------------------- MODULE DijkstraTokenRing ----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, K

VARIABLES value

ASSUME N > 0
ASSUME K > N

Init == /\ value \in [0..N-1 -> 0..K-1]
        /\ (\A i \in 0..N-1 : value[i] = 0)

Next == \/ /\ value[0] = value[N-1]
           /\ value' = [value EXCEPT ![0] = (value[0] + 1) % K]
         \/ /\ value' = [value EXCEPT {}]
           /\ (\E i \in 1..N-1 : value[i] # value[i-1] => value'[i] = value[i-1])

Spec == SpecFairness <> Init /\ [][Next]_<<value>>

TokenExists == \E i \in 0..N-1 : (i = 0 \/ value[i] # value[i-1])

ExactlyOneToken == /\ TokenExists
                 /\ (\A i, j \in 0..N-1 : i # j => 
                      \/ value[i] = value[i-1]
                      \/ value[j] = value[j-1])

SpecFairness == WF_<<value>>(Next)

THEOREM Spec => []TokenExists

THEOREM Spec => <><ExactlyOneToken>

=============================================================================