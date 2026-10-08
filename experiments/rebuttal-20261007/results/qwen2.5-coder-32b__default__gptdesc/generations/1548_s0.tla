------------------------------- MODULE OneStepConsensus -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, F, T, PROPOSALS

VARIABLES sent, received, faulty, states

Init == /\ sent = [p \in 1..N -> {}]
        /\ received = [p \in 1..N -> {}]
        /\ faulty = {}
        /\ states = [p \in 1..N -> "undecided"]

Next ==
    \/ \E p \in 1..N \ faulty : 
         /\ states[p] = "undecided"
         /\ sent' = [sent EXCEPT ![p] = {<<v>> \ v \in PROPOSALS}]
         /\ received' = received
         /\ faulty' = faulty
         /\ states' = states
    \/ \E p \in 1..N \ faulty :
         /\ states[p] = "undecided"
         /\ sent' = [sent EXCEPT ![p] = {}]
         /\ received' = received
         /\ faulty' = faulty
         /\ states' = states
    \/ \E p \in 1..N, m \in sent[p] :
         /\ states[p] = "undecided"
         /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
         /\ sent' = sent
         /\ faulty' = faulty
         /\ states' = [states EXCEPT ![p] = IF Cardinality({v \in PROPOSALS : <<v>> \in received[p]}) >= T 
                                      THEN CHOOSE v \in PROPOSALS : Cardinality({<<v>> \in received[p]}) >= T
                                      ELSE "undecided"]
    \/ \E p \notin faulty :
         /\ states[p] = "undecided"
         /\ faulty' = faulty \cup {p}
         /\ sent' = sent
         /\ received' = received
         /\ states' = states

Spec ==
    /\ Init
    /\ [][Next]_<<sent, received, faulty, states>>
    /\ WF_next(<<sent, received, faulty, states>>)

Safety == 
    \/ \A p \in 1..N : states[p] \in PROPOSALS \/ states[p] = "undecided"
    \/ \E v \in PROPOSALS : \A p \in 1..N : states[p] = v

Liveness ==
    \/ \E v \in PROPOSALS : <>[](\A p \in 1..N : states[p] = v)

=============================================================================