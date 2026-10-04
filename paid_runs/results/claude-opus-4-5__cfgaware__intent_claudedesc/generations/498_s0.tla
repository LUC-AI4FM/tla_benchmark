---------------------------- MODULE Consensus ----------------------------

CONSTANTS Values, Slots

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> Values \cup {NULL}]

NULL == CHOOSE x : x \notin Values

Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> NULL]

Propose(v) ==
    /\ v \in Values
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

Choose(s, v) ==
    /\ s \in Slots
    /\ v \in Values
    /\ v \in proposed
    /\ chosen[s] = NULL
    /\ chosen' = [chosen EXCEPT ![s] = v]
    /\ UNCHANGED proposed

Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E s \in Slots, v \in Values : Choose(s, v)

Fairness ==
    /\ \A v \in Values : WF_vars(Propose(v))
    /\ \A s \in Slots, v \in Values : WF_vars(Choose(s, v))

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ Fairness

Nontriviality ==
    [](\A s \in Slots : chosen[s] # NULL => chosen[s] \in proposed)

Stability ==
    \A s \in Slots : \A v \in Values :
        [](chosen[s] = v => [](chosen[s] = v))

Consistency ==
    [](\A s \in Slots : chosen[s] # NULL =>
        \A v \in Values : (chosen[s] = v => [](chosen[s] = v \/ chosen[s] = NULL)))

ConsistencySimple ==
    [](\A s \in Slots : \A v1, v2 \in Values :
        (chosen[s] = v1 /\ chosen[s] = v2) => v1 = v2)

Liveness ==
    \A s \in Slots : <>(chosen[s] # NULL)

==========================================================================