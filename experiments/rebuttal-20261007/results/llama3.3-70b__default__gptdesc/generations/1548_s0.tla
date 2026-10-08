```
MODULE OneStepConsensus
EXTENDS Integers, FiniteSets

CONSTANTS N, F, T
ASSUME N > 2 * F
ASSUME T == N - F

VARIABLES sent, received, faulty, state

Init ==
  /\ sent = [i \in 1..N |-> {}]
  /\ received = [i \in 1..N |-> {}]
  /\ faulty = {}
  /\ state = [i \in 1..N |-> "propose"]

Next ==
  \/ \E i \in 1..N :
    /\ state[i] = "propose"
    /\ sent' = [sent EXCEPT ![i] = {"propose"}]
    /\ received' = received
    /\ faulty' = faulty
    /\ state' = [state EXCEPT ![i] = "sent"]
  \/ \E i \in 1..N :
    /\ state[i] = "sent"
    /\ Card(received[i]) < T
    /\ \E msg \in {"propose", "decide"} :
      /\ received' = [received EXCEPT ![i] = received[i] \cup {msg}]
      /\ sent' = sent
      /\ faulty' = faulty
      /\ state' = [state EXCEPT ![i] = "receive"]
  \/ \E i \in 1..N :
    /\ state[i] = "receive"
    /\ Card(received[i]) >= T
    /\ \E msg \in {"decide"} :
      /\ received' = received
      /\ sent' = [sent EXCEPT ![i] = {}]
      /\ faulty' = faulty
      /\ state' = [state EXCEPT ![i] = "decide"]
  \/ \E i \in 1..N :
    /\ i \notin faulty
    /\ faulty' = faulty \cup {i}
    /\ sent' = sent
    /\ received' = received
    /\ state' = state

Spec ==
  Init /\ [][Next]_<<sent, received, faulty, state>>
 WF_<<sent, received, faulty, state>>(Next)

THEOREM Spec => [](\A i, j \in 1..N : state[i] = "decide" => state[j] = "decide")
THEOREM Spec => <>(\E i \in 1..N : state[i] = "decide")

All0Init ==
  Init /\ \A i \in 1..N : sent[i] = {"propose"}

All1Init ==
  Init /\ \A i \in 1..N : sent[i] = {"propose"}
```