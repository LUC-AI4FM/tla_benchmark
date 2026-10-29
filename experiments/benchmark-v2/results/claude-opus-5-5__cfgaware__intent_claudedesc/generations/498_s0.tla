---------------------------- MODULE MultiConsensus ----------------------------
EXTENDS FiniteSets

CONSTANTS Values, Slots

ASSUME Values # {} /\ Slots # {}

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

Propose(v) ==
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

Choose(s, v) ==
    /\ chosen[s] = {}
    /\ v \in proposed
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E s \in Slots, v \in Values : Choose(s, v)

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ WF_vars(Next)

Nontriviality ==
    [](\A s \in Slots : chosen[s] \subseteq proposed)

Stability ==
    \A s \in Slots, v \in Values :
        [](v \in chosen[s] => [](v \in chosen[s]))

Consistency ==
    [](\A s \in Slots : Cardinality(chosen[s]) <= 1)

Liveness ==
    \A s \in Slots : <>(chosen[s] # {})

=============================================================================