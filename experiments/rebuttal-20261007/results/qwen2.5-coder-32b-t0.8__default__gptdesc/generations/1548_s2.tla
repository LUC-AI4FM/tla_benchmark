----------------------------- MODULE ByzantineConsensus -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, F, T, ProcessSet \* N: number of processes, F: number of faulty processes, T: threshold parameter, ProcessSet: set of all processes

VARIABLES sent, received, faulty, states \* sent[proc]: messages sent by proc, received[proc]: messages received by proc, faulty: set of faulty processes, states[proc]: state of process proc (0 or 1)

Init == /\ sent = [p \in ProcessSet |-> {}]
        /\ received = [p \in ProcessSet |-> {}]
        /\ faulty = {}
        /\ states = [p \in ProcessSet |-> 0] \/ states = [p \in ProcessSet |-> 1]

Propose(v) == /\ v \in {0, 1}
              /\ \E p \notin faulty : sent' = [sent EXCEPT ![p] = sent[p] \cup {v}]
                                      /\ received' = received
                                      /\ faulty' = faulty
                                      /\ states' = states

Receive(p, v) == /\ p \in ProcessSet
                 /\ v \in {0, 1}
                 /\ ~ (p \in faulty)
                 /\ \E q \notin faulty : v \in sent[q]
                 /\ received'[p] = received[p] \cup {v}
                 /\ sent' = sent
                 /\ faulty' = faulty
                 /\ states' = states

Decide(p, v) == /\ p \in ProcessSet
                /\ v \in {0, 1}
                /\ ~ (p \in faulty)
                /\ Cardinality({x \in received[p] : x = v}) >= T - F
                /\ states'[p] = v
                /\ sent' = sent
                /\ received' = received
                /\ faulty' = faulty

BecomeFaulty(p) == /\ p \in ProcessSet
                   /\ ~ (p \in faulty)
                   /\ faulty' = faulty \cup {p}
                   /\ sent' = [q \in ProcessSet |-> IF q = p THEN {} ELSE sent[q]]
                   /\ received' = [q \in ProcessSet |-> IF q = p THEN {} ELSE received[q]]
                   /\ states' = [q \in ProcessSet |-> IF q = p THEN 0 ELSE states[q]]

Next == \/ \E v \in {0, 1} : Propose(v)
        \/ \E p \in ProcessSet, v \in {0, 1} : Receive(p, v)
        \/ \E p \in ProcessSet, v \in {0, 1} : Decide(p, v)
        \/ \E p \in ProcessSet : BecomeFaulty(p)

Spec == Init /\ [][Next]_<<sent, received, faulty, states>>

\* Safety properties
SafetyFair == [](\/ \E p \in ProcessSet, v \in {0, 1} : ~ (p \in faulty) => <>Decide(p, v))

\* Liveness properties
LivenessAllZero == \/ \A p \in ProcessSet : states[p] = 0
                 \/ \A p \in ProcessSet : states[p] /= 0

LivenessAllOne == \/ \A p \in ProcessSet : states[p] = 1
                \/ \A p \in ProcessSet : states[p] /= 1

Liveness == LivenessAllZero /\ LivenessAllOne

CompleteSpec == Spec /\ SafetyFair /\ Liveness

WF_spec == WF_vars(Next, <<sent, received, faulty, states>>)

=============================================================================