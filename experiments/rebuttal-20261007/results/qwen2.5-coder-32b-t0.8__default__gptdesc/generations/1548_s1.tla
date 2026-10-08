------------------------------- MODULE OneStepConsensus -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    N,  \* Number of processes
    F,  \* Maximum number of faulty processes
    T   \* Threshold parameter for consensus

VARIABLES 
    sent,        \* Set of messages sent by each process (p, v)
    received,    \* Set of messages received by each process (p, v)
    state,       \* State of each process: {proposing, decided}
    value,       \* Proposed or decided value for each process
    faulty       \* Set of faulty processes

Init == 
    /\ sent = [p \in 1..N -> {}]
    /\ received = [p \in 1..N -> {}]
    /\ state = [p \in 1..N -> proposing]
    /\ value = [p \in 1..N -> CHOOSE v \in {0, 1}]
    /\ faulty \in SUBSET (1..N) 
    /\ Cardinality(faulty) <= F

Next == \/ \/ \* Proposing phase
            \/ \E p \in 1..N \ : state[p] = proposing /\ \* Process proposes its value
               (\E v \in {0, 1} : sent' = [sent EXCEPT ![p] = {(p, v)}]
                             /\ received' = [received EXCEPT ![p] = received[p] \cup {(p, v)}]
                             /\ state' = [state EXCEPT ![p] = decided]
                             /\ value' = [value EXCEPT ![p] = v])
           \/ \/ \* Receiving phase
               \/ \E p \in 1..N \ : state[p] = proposing /\ \* Process receives messages
                  (\E m \in SUBSET (DOMAIN received[p]) :
                     LET new_received = received[p] \cup {m}
                     IN received' = [received EXCEPT ![p] = new_received]
                        /\ sent' = sent
                        /\ state' = [state EXCEPT ![p] = 
                            IF Cardinality({v \in {0, 1} : 
                                Cardinality({msg \in new_received : msg[2] = v}) >= T - Cardinality(faulty)}) > 0
                            THEN decided
                            ELSE proposing]
                        /\ value' = [value EXCEPT ![p] = CHOOSE v \in {0, 1} :
                            IF Cardinality({msg \in new_received : msg[2] = v}) >= T - Cardinality(faulty)}
           \/ \/ \* Faulty processes
               \/ \E p \in faulty \: /\ sent' = [sent EXCEPT ![p] = {}]
                                       /\ received' = [received EXCEPT ![p] = {}]
                                       /\ state' = [state EXCEPT ![p] = decided]
                                       /\ value' = [value EXCEPT ![p] = CHOOSE v \in {0, 1}]
                                       /\ faulty' = faulty

Spec == Init /\ [][Next]_<<sent, received, state, value>>

\* Safety properties
TypeInvariant ==
    /\ sent \in [1..N -> SUBSET ([1..N] \X {0, 1})]
    /\ received \in [1..N -> SUBSET ([1..N] \X {0, 1})]
    /\ state \in [1..N -> {proposing, decided}]
    /\ value \in [1..N -> {0, 1}]
    /\ faulty \in SUBSET (1..N)

DecidedValueAgreement ==
    \/ \A p, q \in 1..N : state[p] = decided /\ state[q] = decided => value[p] = value[q]
    \/ \E v \in {0, 1} : \A p \in 1..N : state[p] = decided => value[p] = v

\* Liveness properties
Safety == Spec /\ []TypeInvariant /\ []DecidedValueAgreement

Fairness ==
    WF_next(\A p \in (1..N) \ fault : <<p>>)

THEOREM Spec => Safety /\ Fairness
=============================================================================