---------------------------- MODULE OneStepConsensus ----------------------------

CONSTANTS N, F, T \* Number of processes, number of Byzantine faults, threshold

VARIABLES sent, received, faulty, state \* sent[i][j] = message from i to j, received[i] = set of messages received by i, faulty = set of faulty processes, state[i] = process i's decision

\* Process states
CONSTANT UNDECIDED, DECIDE_0, DECIDE_1

\* Type invariants
TypeOK == /\ sent \in [1..N -> [1..N -> {UNDECIDED, 0, 1}}]
          /\ received \in [1..N -> SUBSET {0, 1}]
          /\ faulty \in SUBSET (1..N)
          /\ state \in [1..N -> {UNDECIDED, DECIDE_0, DECIDE_1}]

\* Initial predicate for all-0 proposal
Init0 == /\ sent = [i \in 1..N |-> [j \in 1..N |-> UNDECIDED]]
         /\ received = [i \in 1..N |-> {}]
         /\ faulty = {}
         /\ state = [i \in 1..N |-> UNDECIDED]

\* Initial predicate for all-1 proposal
Init1 == /\ sent = [i \in 1..N |-> [j \in 1..N |-> UNDECIDED]]
         /\ received = [i \in 1..N |-> {}]
         /\ faulty = {}
         /\ state = [i \in 1..N |-> UNDECIDED]

\* Action: A process proposes a value
Propose(v) == CHOOSE i \in (1..N) \ faulty:
                /\ sent' = [sent EXCEPT ![i] = [j \in 1..N |-> v]]
                /\ received' = received
                /\ faulty' = faulty
                /\ state' = state

\* Action: A process receives messages and decides
Receive == CHOOSE i \in (1..N) \ faulty:
               LET msgs == UNION {received[i]}
               IN  /\ sent' = sent
                   /\ received' = [received EXCEPT ![i] = msgs]
                   /\ faulty' = faulty
                   /\ IF Cardinality({m \in msgs : m = 0}) >= T
                      THEN state' = [state EXCEPT ![i] = DECIDE_0]
                      ELSE IF Cardinality({m \in msgs : m = 1}) >= T
                           THEN state' = [state EXCEPT ![i] = DECIDE_1]
                           ELSE state' = state

\* Action: A process becomes faulty
BecomeFaulty == CHOOSE i \in (1..N) \ faulty:
                  /\ sent' = sent
                  /\ received' = received
                  /\ faulty' = faulty \cup {i}
                  /\ state' = [state EXCEPT ![i] = UNDECIDED]

\* Next-state relation
Next == \/ \E v \in {0, 1} : Propose(v)
        \/ Receive
        \/ BecomeFaulty

\* Specification
Spec == Init0 \/ Init1 /\ [][Next]_<<sent, received, faulty, state>>

\* LTL properties for all-0 and all-1 proposals
OneStep0_Ltl == Spec /\ [](Init0 -> <>[](\A i \in 1..N : state[i] = DECIDE_0))
OneStep1_Ltl == Spec /\ [](Init1 -> <>[](\A i \in 1..N : state[i] = DECIDE_1))

\* Liveness property: all processes eventually decide
AllDecideOne == Spec /\ [](<>[](\A i \in 1..N : state[i] \in {DECIDE_0, DECIDE_1}))

===============================================================================