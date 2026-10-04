-------------------------------- MODULE MultiInstanceConsensus --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Slots

ASSUME ValuesNonempty == Values # {}
ASSUME SlotsNonempty == Slots # {}

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeInvariant ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]
    /\ \A s \in Slots : IsFiniteSet(chosen[s])

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

Propose(v) ==
    /\ v \in Values
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

Choose(s, v) ==
    /\ s \in Slots
    /\ v \in proposed
    /\ chosen[s] = {}
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E s \in Slots, v \in Values : Choose(s, v)

Fairness ==
    /\ \A v \in Values : WF_vars(Propose(v))
    /\ \A s \in Slots, v \in Values : WF_vars(Choose(s, v))

Spec == Init /\ [][Next]_vars /\ Fairness

ChosenValuesWereProposed ==
    \A s \in Slots : chosen[s] \subseteq proposed

AtMostOneChosenPerSlot ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

ChosenPersistent ==
    [][
        \A s \in Slots : 
            chosen[s] # {} => chosen'[s] = chosen[s]
    ]_vars

Safety ==
    /\ ChosenValuesWereProposed
    /\ AtMostOneChosenPerSlot

Liveness ==
    \A s \in Slots : <>(chosen[s] # {})

FullSpec == Spec

THEOREM Spec => []TypeInvariant
THEOREM Spec => []Safety
THEOREM Spec => ChosenPersistent
THEOREM Spec => Liveness

=============================================================================