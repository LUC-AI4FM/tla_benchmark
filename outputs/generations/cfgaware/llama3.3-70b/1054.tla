---------------------------- MODULE TokenRing ----------------------------
EXTENDS Integers

CONSTANT N, M
VARIABLE counters, tokenPresent

Init ==
  /\ counters = [i \in 0..N-1 |-> 0]
  /\ tokenPresent = << >>

Next ==
  /\ IF (counters[0] < M-1) 
    THEN counters' = [counters EXCEPT ![0] = (counters[(N-1)] + 1) % M]
    ELSE counters' = counters
  /\ FORALL (i \in 1..N-1) 
    DO IF (counters[i-1] # counters[i]) 
       THEN counters' = [counters' EXCEPT ![i] = counters[i-1]]
       ELSE counters' = counters'
  /\ tokenPresent' = << >>
  
Stabilization ==
  <>[]<>(\E i \in 0..N-1 : counters[i] = counters[(i+1)%N])

Spec == Init /\ [][Next]_counters

THEOREM Spec => []Stabilization
=============================================================================