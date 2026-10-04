---------------------------- MODULE Consensus ----------------------------

CONSTANTS Values, Slots

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]
    /\ \A s \in Slots : Cardinality(chosen[s]) \leq 1

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

Propose(v) ==
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

Decide(s, v) ==
    /\ v \in proposed
    /\ chosen[s] = {}
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

ProposeAction ==
    \E v \in Values : Propose(v)

DecideAction ==
    \E s \in Slots : \E v \in Values : Decide(s, v)

Next ==
    \/ ProposeAction
    \/ DecideAction

Fairness ==
    /\ WF_vars(ProposeAction)
    /\ \A s \in Slots : WF_vars(\E v \in Values : Decide(s, v))

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ Fairness

SafetyChosenWasProposed ==
    \A s \in Slots : \A v \in chosen[s] : v \in proposed

SafetyAtMostOneChosen ==
    \A s \in Slots : Cardinality(chosen[s]) \leq 1

SafetyPersistence ==
    [][
        \A s \in Slots : \A v \in Values :
            (v \in chosen[s]) => (v \in chosen'[s])
    ]_vars

Safety ==
    /\ SafetyChosenWasProposed
    /\ SafetyAtMostOneChosen
    /\ SafetyPersistence

Liveness ==
    \A s \in Slots : <>(chosen[s] # {})

==========================================================================