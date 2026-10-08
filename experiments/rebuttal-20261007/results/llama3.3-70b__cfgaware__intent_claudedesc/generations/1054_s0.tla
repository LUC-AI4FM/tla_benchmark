---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, M
VARIABLE counters

vars == <<counters>>

Init ==
  /\ counters \in [1..N -> 0..M-1]
  /\ N <= M + 1

Next(i \in 1..N) ==
  IF i = 1 THEN
    /\ (counters[1] = counters[N] => counters' = [counters EXCEPT ![1] = (counters[1] + 1) % M])
    /\ (counters[1] # counters[N] => counters' = [counters EXCEPT ![1] = counters[N]])
  ELSE
    /\ (counters[i] = counters[i-1] => counters' = counters)
    /\ (counters[i] # counters[i-1] => counters' = [counters EXCEPT ![i] = counters[i-1]])

Next ==
  \E i \in 1..N : Next(i)

Spec == Init /\ [][Next]_vars

Stabilization ==
  <>[]\E t \in 0..M-1 : 
    (\A i \in 1..N-1 : counters[i] = counters[1]) 
    /\ (counters[N] = counters[1] \/ counters[N] = (counters[1] - 1 + 1) % M)

THEOREM Spec => WF_vars(Next) => Stabilization
=============================================================================