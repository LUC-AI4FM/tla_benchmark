---------------------------- MODULE MultiSlotConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Values, Slots

VARIABLES proposed, chosen

vars == <<proposed, chosen>>

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]
    /\ \A s \in Slots : Cardinality(chosen[s]) <= 1

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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: Nontriviality - only proposed values can be chosen
Nontriviality ==
    \A s \in Slots : chosen[s] \subseteq proposed

\* Safety: Stability of proposed values - once proposed, always proposed
ProposedStability ==
    [][proposed \subseteq proposed']_vars

\* Safety: Stability of chosen values - once chosen, the value doesn't change
ChosenStability ==
    \A s \in Slots : [][chosen[s] /= {} => chosen[s] = chosen'[s]]_vars

\* Safety: Per-slot consistency - at most one value chosen per slot
Consistency ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ Nontriviality
    /\ Consistency

\* Liveness: Eventually every slot becomes nonempty (assuming values exist)
AllSlotsEventuallyChosen ==
    \A s \in Slots : <>(chosen[s] /= {})

\* Liveness: If a value is proposed, it can eventually be chosen for some slot
\* (This is a possibility, not guaranteed for all values)
EventualProgress ==
    (proposed /= {} /\ \E s \in Slots : chosen[s] = {}) ~> 
    (\E s \in Slots : chosen[s] /= {})

=============================================================================