------------------------------ MODULE DijkstraTokenRing ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, K
ASSUME N > 0 /\ K > N

VARIABLES v

NextIndex(i) == (i + 1) MOD N

Init == \E initVals \in [0 .. N-1 -> 0 .. K-1] : v = initVals

ProcessRule(i) ==
  IF i = 0 THEN
      /\ v[0] = v[N-1]
      /\ v' = [v EXCEPT ![0] = (v[0]+1) MOD K]
  ELSE
      /\ v[i] # v[i-1]
      /\ v' = [v EXCEPT ![i] = v[i-1]]

Next == \E i \in 0 .. N-1 : ProcessRule(i)

TokenExists == \E i \in 0 .. N-1 : v[i] # v[NextIndex(i)]

ExactlyOneToken ==
  \E i \in 0 .. N-1 :
      (v[i] # v[NextIndex(i)]) /\ (\A j \in 0 .. N-1 : j /= i => v[j] = v[NextIndex(j)])

Spec == Init /\ [][Next]_v /\ WF_(i \in 0 .. N-1) ProcessRule(i)

SafetyInvariant == TokenExists

LivenessProperty == \square \Diamond ExactlyOneToken

THEOREM Spec => SafetyInvariant
THEOREM Spec => LivenessProperty

=============================================================================