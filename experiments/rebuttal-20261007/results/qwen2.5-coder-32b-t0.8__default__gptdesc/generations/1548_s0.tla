```tla
MODULE OneStepConsensus

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N, F, T \* Number of processes, number of faulty processes, threshold parameter

VARIABLES sent, received, faulty, states \* sent[i] = message sent by process i, received[i] = set of messages received by process i, faulty = set of faulty processes, states[i] = state of process i (0, 1, or decided value)

Init == /\ sent = [i \in 1..N -> <<>>]
        /\ received = [i \in 1..N -> {}]
        /\ faulty = {}
        /\ \/ states = [i \in 1..N -> 0] 
           \/ states = [i \in 1..N -> 1]

Propose == CHOOSE i \in (1..N) \ faulty: /\ sent' = [sent EXCEPT ![i] = <<states[i]>>]
                                            /\ UNCHANGED received
                                            /\ UNCHANGED faulty
                                            /\ UNCHANGED states

Receive == CHOOSE i \in 1..N, m \in UNION {sent[j]: j \in (1..N) \ {i}}: /\ received' = [received EXCEPT ![i] = received[i] \cup {m}]
                                                                                 /\ UNCHANGED sent
                                                                                 /\ UNCHANGED faulty
                                                                                 /\ UNCHANGED states

Decide == CHOOSE i \in 1..N, v \in {0, 1}: \/ /\ Cardinality({j \in (1..N) : <<v>> \in received[j]} \ {i}) >= T 
                                                /\ states' = [states EXCEPT ![i] = v]
                                            /\ \/ \/ UNCHANGED sent
                                                   /\ UNCHANGED received
                                                   /\ UNCHANGED faulty
                                               \/ /\ sent' = [sent EXCEPT ![i] = <<v>>]
                                                  /\ received' = [received EXCEPT ![i] = {}]
                                                  /\ faulty' = {}
                                                  /\ states = [states EXCEPT ![i] = v]

BecomeFaulty == CHOOSE i \in 1..N: /\ faulty' = faulty \cup {i}
                                      /\ UNCHANGED sent
                                      /\ UNCHANGED received
                                      /\ UNCHANGED states

Next == \/ Propose
        \/ Receive
        \/ Decide
        \/ BecomeFaulty

Spec == Init /\ [][Next]_<<sent, received, faulty, states>>

Invariant1 == \A i \in 1..N: Cardinality({j \in (1..N) : <<states[i]>> \in received[j]} \ {i}) >= T => states[i] = decidedValue

Invariant2 == \A i \in 1..N: Cardinality(faulty) > F => states[i] \notin {0, 1}

Fairness == WF_next(Next)

THEOREM Spec => []Invariant1
THEOREM Spec => []Invariant2
```