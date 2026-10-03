--------------------------- MODULE OneStepConsensus ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, F, T
VARIABLES sent, received, faulty, state

TypeOK == (N >= 2) /\ (F < N) /\ (T = N - F)

OneStep0_Ltl == <>[](~(AllDecideOne))
OneStep1_Ltl == <>[](AllDecideOne)

AllDecideOne == \A i \in 1..N : state[i] = 1

Spec ==
  /\ sent = [i \in 1..N |-> 0]
  /\ received = [i \in 1..N |-> {}]
  /\ faulty = {}
  /\ state = [i \in 1..N |-> 0]
  /\ WF_vars({Propose, Receive, Decide, BecomeFaulty}, sent, received, faulty, state)

Propose(i) == 
  /\ i \in 1..N
  /\ sent' = [sent EXCEPT ![i] = sent[i] + 1]
  /\ received' = received
  /\ faulty' = faulty
  /\ state' = state

Receive(i, j) == 
  /\ i \in 1..N
  /\ j \in 1..N
  /\ i # j
  /\ sent[j] > 0
  /\ received' = [received EXCEPT ![i] = received[i] \cup {j}]
  /\ sent' = sent
  /\ faulty' = faulty
  /\ state' = state

Decide(i) == 
  /\ i \in 1..N
  /\ Card(received[i]) >= T
  /\ state' = [state EXCEPT ![i] = 1]
  /\ sent' = sent
  /\ received' = received
  /\ faulty' = faulty

BecomeFaulty(i) == 
  /\ i \in 1..N
  /\ i \notin faulty
  /\ faulty' = faulty \cup {i}
  /\ sent' = sent
  /\ received' = received
  /\ state' = state

Next ==
  \/ \E i \in 1..N : Propose(i)
  \/ \E i, j \in 1..N : Receive(i, j)
  \/ \E i \in 1..N : Decide(i)
  \/ \E i \in 1..N : BecomeFaulty(i)

THEOREM Spec => []TypeOK
=============================================================================