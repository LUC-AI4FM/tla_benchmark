------------------------------- MODULE MultiSlotConsensus -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Slots, Values

VARIABLES proposed, chosen

Init == /\ proposed \in SUBSET Values
        /\ chosen \in [Slots -> {}]

Next ==
    \/ \E v \notin proposed: 
         /\ UNCHANGED [proposed' EXCEPT ! = proposed \cup {v}]
         /\ UNCHANGED chosen'
    \/ \E s \in Slots, v \in proposed:
         /\ chosen[s] = {}
         /\ UNCHANGED proposed'
         /\ chosen' = [chosen EXCEPT ![s] = {v}]

Spec ==
    /\ Init
    /\ [][Next]_<<proposed, chosen>>
    /\ WF_next(<<proposed, chosen>>)

TypeCorrectness ==
    /\ proposed \in SUBSET Values
    /\ chosen \in [Slots -> (SUBSET Values)]

Nontriviality ==
    \/ proposed = {}
    \/ \E s \in Slots: chosen[s] /= {}

Stability ==
    \A v \notin proposed:
        \A <<proposed0, chosen0>, <proposed1, chosen1>> \in Run(Spec):
            /\ v \notin proposed0
            => v \notin proposed1

PerSlotConsistency ==
    \A s \in Slots:
        \A <<proposed0, chosen0>, <proposed1, chosen1>> \in Run(Spec):
            /\ chosen0[s] = {}
            => chosen0[s] = chosen1[s]

Liveness ==
    WF_next(<<proposed, chosen>>) ->>
        \A s \in Slots: <><chosen'[s] /= {}>_<<proposed, chosen>>

THEOREM Spec =>
    TypeCorrectness
    /\ Nontriviality
    /\ Stability
    /\ PerSlotConsistency
    /\ Liveness

=============================================================================